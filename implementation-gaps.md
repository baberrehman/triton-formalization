# Where the formal model rejects a program Triton-Ascend still accepts

Date: 2026-10-30.

This note compares the two Lean calculi in this directory with the checkers that ship in `triton-ascend`. A row is included only when the calculus rejects the program and the Python checker accepts it, and the acceptance has a concrete consequence in the compiler. Agreement, and the places where Python is the stricter checker, are listed at the end so they are not mistaken for bugs.

The Triton calculus is the dtype, rank, broadcast, and mask rules in `Triton/Typing.lean`. TAS is the cube/vector calculus in `TAS/`. Neither is a model of the whole pipeline. The integer payload is not a tensor element, and TAS does not compute a matrix product.

## 1. `tl.load` accepts a non-boolean mask

`maskOk` in `Triton/Typing.lean` allows a mask only when it is `scalar bool` or `tensor bool` of a shape that broadcasts to the result. `bad_mask_rejected` is that rule on an `f32` mask.

`TritonSemantic.load` does not apply it. `_load_legacy` (`python/triton/language/semantic.py`) checks that a scalar pointer is not given a block mask, broadcasts the mask to the pointer, and passes `mask.handle` to `create_masked_load`. The same file rejects the same mask on a store:

```1280:1283:triton-ascend/python/triton/language/semantic.py
        if mask is None:
            return self.tensor(self.builder.create_store(ptr.handle, val.handle, cache, eviction), tl.void)
        if not mask.type.scalar.is_bool():
            raise ValueError("Mask must have boolean scalar type")
```

A direct call with an `f32` mask of shape `[128]` returns an `fp32` tensor from `semantic.load`. The operation it inserts is illegal. `tt.load` requires the mask operand to be `TT_BoolLike` (`TritonOps.td`: "1-bit signless integer or ranked tensor of 1-bit signless integer values"). Building the op and calling `module.verify()` reports:

```text
'tt.load' op operand #1 must be 1-bit signless integer or ranked tensor of
1-bit signless integer values, but got 'tensor<128xf32>'
```

`ast_to_ttir` reaches that verifier only after the body has been visited (`code_generator.py`, `module.verify()`). The failure is `RuntimeError: error encountered during parsing`, not the "Mask must have boolean scalar type" error that `store` raises. An `int1` mask of the same shape verifies. `correspondence/check_link.py` records the Python acceptance as `test_load_f32_mask_is_accepted_by_semantic_py`.

What goes wrong: the Python type checker returns a value for a load whose mask is not a predicate. The first rejection is the MLIR verifier. Any caller of `TritonSemantic` that does not verify the module is holding an illegal `tt.load`.

## 2. `atomic_add` accepts a non-boolean mask

`tt.atomic_rmw` has the same `Optional<TT_BoolLike>` mask operand. `atom_red_typechecking_impl` broadcasts a provided mask and does not test `mask.type.scalar.is_bool()`. `histogram` in the same file does test it.

`semantic.atomic_add` of an `f32` pointer block, an `f32` value, and an `f32` mask returns normally and inserts:

```text
%9 = "tt.atomic_rmw"(%4, %6, %8) ... : (tensor<128x!tt.ptr<f32>>, tensor<128xf32>, tensor<128xf32>) -> tensor<128xf32>
```

`module.verify()` fails with operand #2 required to be a 1-bit integer, got `tensor<128xf32>`. The Lean rule for a masked load is the same predicate requirement; the atomic path in `semantic.py` skips the check that `store` and `histogram` already perform.

## 3. `tl.where` casts a non-boolean condition

`ternaryTy` for `where_` accepts a condition only when it is `scalar bool` or `tensor bool`. `semantic.where` warns and then casts:

```1668:1673:triton-ascend/python/triton/language/semantic.py
    def where(self, condition: TensorTy, x: TensorTy, y: TensorTy) -> TensorTy:
        if condition.dtype != tl.int1:
            warnings.warn(
                f"tl.where with a non-boolean condition is deprecated and will error out in a future triton release. Got {condition.dtype}"
            )
        condition = self.cast(condition, tl.int1)
```

An `f32` condition of shape `[128]` produces a warning and an `fp32` result. The IR is a cast to `i1` followed by `select`, so `module.verify()` is not the failure. The predicate is whatever that cast does to the float, and the warning says a future release will reject it. The calculus rejects it now.

## 4. A cube DMA or `mmad` inside a vector scope

TAS `copyOk` accepts five pairs, each tied to the core that is open:

| Open core | Source | Destination |
|---|---|---|
| cube | GM | L1 |
| cube | L0C | UB |
| cube | L0C | GM |
| neither | GM | UB |
| neither | UB | GM |

`checkMmad` accepts `mmad` only when the open core is cube and the three buffers are L1, L1, and L0C. A GM-to-L1 copy inside a vector scope is `none`. A GM-to-UB copy inside cube is `none`.

The Python front end splits those two facts across two checkers, and neither sees both.

`scope_check.py` records the birth core of a name. `tla.copy` and `tla.cube.mmad` are calls. They load names and do not assign them, so a copy of buffers allocated outside either scope passes the birth-core walk in either core.

`tla.copy` (`third_party/ascend/language/tla/copy.py`) checks the space pair and not the enclosing `with`:

- `("gm", "ub")` emits `hivm.load`
- `("ub", "gm")` emits `hivm.store`
- `("gm", "l1")` emits `hivm.nd2nz`
- source space `"l0c"` emits `hivm.fixpipe` for every destination space

`tla.cube.mmad` checks that `a` and `b` are L1 and `acc` is L0C. It does not check that the call is inside `tla.scope.cube()`.

`hivm.nd2nz` is declared with `CubeCoreTypeTrait` (`HIVMDMAOps.td`). `hivm.load` from GM to UB is inferred as `VECTOR` (`LoadOp::inferCoreType`). `SplitMixKernel` clones a mix function into an AIC half and an AIV half and erases the other core's operations from each half (`filterMixFunc`: cube ops are removed from the vector function, vector ops from the cube function). A GM-to-L1 copy written inside `tla.scope.simd()` is therefore a cube operation placed in the vector scope. The front end does not reject it. The split either drops it from the vector half or leaves it on the cube half, separated from the vector operations it was written next to.

The same gap applies to `mmad` inside `simd`, and to a GM-to-UB copy inside `cube`: the space check succeeds, the scope walk succeeds, and the core type of the emitted op does not match the scope the programmer wrote.

This was read from those three files. It was not executed as a device kernel.

## What is not a hole in Triton-Ascend

These are real differences. They are not programs the model catches and the implementation lets through.

- `semantic.arange` requires a power-of-two length. `arange(0, 128)` is accepted by both. `arange(0, 3)` raises `ValueError` in Python. `arange_non_pow2_typed` accepts it as `tensor i32 [3]`. Python is stricter.
- A scalar assigned inside `cube` and read inside `simd` is rejected by `scope_check.py` (`test_scalar_inside_rejected_by_scope_check`). TAS accepts it, because the type stays `scalar` (`scalar_inside_tas_accepted`, `scalar_inside_scope_rejected`). Python is stricter.
- A register assigned in one core and read in the other is rejected by both (`cross_scope_rejected`, `scope_cross_rejected`, and `cross_core_read_scope` / `cross_core_read_tas`).
- `program_id` axis 3, and `dot` of `[32, 16]` with `[32, 16]`, are rejected by both. The matching `dot` of `[32, 16]` with `[16, 8]` is `f32 [32, 8]` in both.
- `logical_and` on `int32` raises `ValueError: Cannot bitcast data-type of size 32 to data-type of size 1`. It does not build an illegal op.
- An unmasked load is well-typed in the calculus and steps. The calculus does not claim to catch an out-of-bounds address. `dot` does not multiply matrices. `dotScaled` does not check the hardware scale layout.
