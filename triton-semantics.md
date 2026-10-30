# Small-step semantics of the Triton language

Date: 2026-10-30. The normative definition is the Lean development in `Triton/` (`Basic.lean`, `Typing.lean`, `Step.lean`, `Examples.lean`, `Safety.lean`). This note records what those files say.

This calculus is the `tl.*` surface in `python/triton/language`. It is separate from TAS. TAS is the cube and vector fragment of TLA; this development does not replace it. The property proved here is the class of checks in `semantic.py`: dtype, rank, broadcast, mask, and a scalar condition on `if`. It is not IEEE arithmetic, data-race freedom, or a proof that an unmasked load stays inside an allocation.

## Values

A shape is a `List Nat`. The empty shape is a scalar. `numel` of `[]` is 1; otherwise it is the product of the extents. `maxNumel` is 1048576, the same bound as `TRITON_MAX_TENSOR_NUMEL`.

Dtypes are `bool`, the signed, unsigned, and pointer-sized integers, `pi32`, and the floating types used by Triton (`f16`, `bf16`, `f32`, `f64`, and the `f8*` encodings). `bool` is not numeric. `isFloat`, `isInt`, and `isNumeric` are the predicates the operator rules use.

A type is a scalar, a tensor, a scalar pointer, a tensor of pointers, a block pointer, a tensor descriptor, or a pair. A value is the same tag plus one `Int` (an address is a `Nat` stored as that integer). `valTy` drops the integer. `pack` rebuilds a value of a given type from an integer, and `valTy (pack t n) = t`.

Broadcast is right-aligned, as in `broadcast_impl`. The shorter shape is padded with leading ones. An axis matches when the extents are equal or either side is 1. Scalars have shape `[]`.

`constexpr` bounds, block shapes, and axes are `Nat` arguments of the syntax. They are not runtime values. `PropagateNan`, `void`, and the host-side target query are not device expressions. Gluon layouts are out of scope.

## Operations

Every public `tl` operation is one constructor. The typing function depends only on the constructor and the operand types, and a value redex is `pack` of the type that function returns. The integer is a carrier: `evalBinary` adds the payloads, and nothing in the proof reads that sum as a floating-point result.

| Constructor | `tl` names |
|---|---|
| `Float1` | `exp`, `exp2`, `log`, `log2`, `cos`, `sin`, `sqrt`, `sqrt_rn`, `rsqrt`, `erf`, `floor`, `ceil`, `sigmoid` |
| `Num1` | `abs`, `neg` |
| `Arith2` | `add`, `sub`, `mul`, `fdiv`, `div_rn`, `umulhi`, `maximum`, `minimum`, `cdiv` |
| `Bit2` | `and`, `or`, `xor`, `shl`, `shr` |
| `CmpOp` | `eq`, `ne`, `lt`, `le`, `gt`, `ge`. The result is `bool` of the broadcast shape |
| `ReduceOp` | `sum`, `max`, `min`, `xor_sum`, `reduce_or`. `argmax` and `argmin` return a pair of the value and an `i32` index |
| `ScanOp` | `cumsum`, `cumprod`, `associative_scan` |
| `Unary.cast` | `cast`, dtype change, shape kept |
| `Unary.trans`, `permute` | `trans`, `permute`. `permute` requires a permutation of the rank |
| `reshape`, `view` | equal `numel`, and the result `numel` is at most `maxNumel`. Contiguity of `view` is not checked |
| `expandDims`, `sliceAxis`, `ravel`, `zerosLike` | `expand_dims`, slicing, `ravel`, `zeros_like` |
| `sort`, `bitonic`, `flip`, `softmax` | same shape when the axis is in range. `topk` replaces that axis with `k` when `0 < k ≤ dim` |
| `split`, `join`, `interleave`, `cat` | `split` needs a last dimension of 2 and returns a pair. `join` appends `[2]`. `interleave` doubles the last dimension. `cat` adds one axis |
| `dot`, `dotScaled` | rank-2 `[M, K] × [K, N]`, result `[M, N]`. The third argument of `dotScaled` is a pair of tensors. Their layout is not the hardware scale rule |
| `ptrOffset` | pointer plus `i32`. A scalar `i32` keeps a scalar pointer. A tensor `i32` produces a pointer tensor of the broadcast shape |
| `makeBlockPtr`, `makeTDesc` | scalar pointer and a block shape whose `numel` is at most `maxNumel` |
| `advance`, `loadTDesc` | offsets are an `i32` tensor of shape `[rank]` |
| `load`, `loadMask` | the result shape is the pointer shape. A mask is `bool` and broadcasts onto that shape. `other` matches the result dtype and broadcasts onto it |
| `histogram` | integer input, `bins > 0` and `bins ≤ maxNumel`, result `tensor i32 [bins]` |
| `rand` | `rand`, `randn`, `rand4x`, `randn4x`, `uniform`, `normal` give `f32` of the input shape. `randint` and `randint4x` give `i32`. `philox` appends `[4]` |
| `asm`, `map`, `hint` | `inline_asm_elementwise` and `extern_elementwise` (`asm` may change the dtype and keeps the shape; the body is not checked). `map_elementwise` keeps the type. `multiple_of`, `max_contiguous`, and `max_constancy` keep the type |
| `where_` | `where`. The condition is `bool` and broadcasts with the two branches |
| `fma`, `clamp` | three numeric operands, one broadcast shape |
| `swizzle` | two `i32` scalars. The size arguments are `Nat`. The result is `i32` |
| `programId`, `numPrograms` | axis `< 3`, result `scalar i32` |
| `arange` | `start ≤ finish` and the length is at most `maxNumel`. Result `tensor i32 [finish - start]` |
| `full`, `zeros` | `numel` at most `maxNumel` |
| `gather`, `broadcast` | `gather` returns the index shape. `broadcast` requires the result shape to be the second operand's shape |
| `store`, `storeMask`, `storeTDesc` | pointer plus value of the same dtype, broadcasting onto the pointer shape. A block pointer or descriptor is stored with a tensor of the block shape. A descriptor store also requires `i32` offsets of shape `[rank]` |
| `atomic`, `cas` | the result type is the loaded type of the pointer (scalar, or the pointer-tensor shape). The command binds that type |
| `branch` | `if`. The condition is `scalar bool`, and the two branches produce the same context. A tensor condition is rejected; that program is written with `where` |
| `loop` | `range` and `static_range`. See below |
| `deviceAssert`, `staticAssert`, `assume` | the argument is `scalar bool` |
| `devicePrint`, `staticPrint` | the argument has some type |
| `barrier` | `debug_barrier` |

`zeros_like` keeps the operand type. `full` is the tensor form of a splat. Rank is not capped at 8. A shift's right operand must already have the left operand's dtype; there is no promotion. `cdiv` is allowed on tensors by the broadcast rule, not only on `constexpr` scalars.

## Contexts and steps

Names are `Nat`. Contexts and environments are association lists. `lookup` takes the first match. `update` replaces the first binding of that name, or appends the name when it is new. Reassigning a name to the type it already has leaves the context list unchanged.

`models env Γ` says every name in the context has a value of that type in the environment. An extra environment binding is allowed.

`stepE` steps an expression and does not change the environment. `step` steps a command. `Steps cfg` is the reflexive-transitive closure at one fixed program configuration (`pid` and `num_programs` on three axes).

A variable loads the value `models` provides. `program_id`, `num_programs`, `arange`, `full`, and `zeros` step to a value under the same condition that types them. A unary, binary, or ternary expression steps its children left to right, then packs a value of the type returned by `unaryTy`, `binaryTy`, or `ternaryTy`.

`assign` of a value extends the environment and becomes `skip`. `seq skip c` becomes `c`. `block` runs its body; `block skip` becomes `skip`. The result context of `block` is the result context of the body, so an assignment inside the block is visible afterwards. `branch` of a scalar `bool` selects one arm. `loop 0` becomes `skip`. `loop (n+1)` becomes `seq body (loop n body)`.

`store`, `storeMask`, and `storeTDesc` of values become `skip` and do not write a heap. There is no heap. `atomic` and `cas` bind `pack` of the result type. `barrier` becomes `skip`. An assert of a scalar `bool` becomes `skip`. A print of a value becomes `skip`.

An unmasked `load` of a well-typed pointer value always steps. That is not a proof that the address is in bounds.

## Loops

`check` accepts `loop n body` only when `check` of `body` returns the same context list it was given. Because `update` replaces a binding in place, a body may reassign a name that is already in scope at the same type. A body that assigns a fresh name is rejected: the context list grows, so the next iteration would not be checked at the same context. The bound `n` is not inspected by `check`.

## Theorems

All of these are proved in `Triton/Safety.lean`. `lake build` checks them. There is no `sorry`.

| Theorem | Statement |
|---|---|
| `evalUnary_spec`, `evalBinary_spec`, `evalTernary_spec` | A value whose operands are accepted by the typing function steps to `pack` of that type. |
| `expr_progress` | A typed expression is a value, or `stepE` returns a successor. |
| `expr_preservation` | That successor has the same type. |
| `progress` | A typed command is `skip`, or `step` returns a successor. |
| `preservation` | The successor is typed, the new environment matches the new context, and the result context of the original command is unchanged. |
| `type_safety` | Every configuration reachable by `Steps` from a typed command is typed at that same result context. |

## Examples

`Triton/Examples.lean` is checked by `native_decide`.

| Theorem | What it checks |
|---|---|
| `vec_add_typed` | `offs = arange(0, 128)`, a masked-free load through `x + offs`, and a store of `xv + full([128], 1)` through `y + offs`. |
| `bad_mask_rejected` | `load` whose mask is `f32` rather than `bool`. |
| `tensor_if_rejected` | `if` on `arange`, which is not a scalar `bool`. |
| `dot_rejected` | `dot` of `[32, 16]` with `[32, 16]`. The contracting dimensions differ. |
| `dot_typed` | `dot` of `[32, 16]` with `[16, 8]` has type `tensor f32 [32, 8]`. |
| `program_id_typed`, `program_id_rejected` | Axis 0 is `scalar i32`. Axis 3 is rejected. |
| `loop_skip_typed` | `loop` of `skip` keeps the context. |
| `loop_fresh_rejected` | `loop` of an assignment to a name that is not yet in scope. |
| `loop_reassign_typed` | `loop` that reassigns `offs` to another `tensor i32 [128]`. |

## What this development does not claim

The integer in a value is not a tensor element, and `dot` does not multiply matrices. Stores and atomics do not describe a memory. The theorem does not rule out a data race, an unmasked out-of-bounds load, or a `view` that would be illegal because of contiguity. The scale operands of `dotScaled` are a pair of tensors of any shape. Libdevice functions other than the `Float1` list are `Unary.asm`: the dtype may change, the shape stays, and the external body is not given a semantics. `target_info` is host-side.

TAS remains the model of `tla.scope.cube`, `tla.scope.simd`, and the copy directions. Pipeline acceptance between Triton-Ascend stages is `docs/staged-compilation-contracts-triton-ascend.md`.

## Link to semantic.py

`correspondence/check_link.py` calls `TritonSemantic` in `python/triton/language/semantic.py` on the examples in `Triton/Examples.lean`.

Both accept `program_id(0)` as `int32` of rank 0 and reject axis 3. Both reject `dot` of `[32, 16]` with `[32, 16]` and accept `dot` of `[32, 16]` with `[16, 8]` at `f32 [32, 8]`. Both accept `arange(0, 128)` as `int32 [128]`.

Two checks differ. `semantic.arange` requires a power-of-two range, so `arange(0, 3)` raises `ValueError`; `arange_non_pow2_typed` accepts it as `tensor i32 [3]`. `semantic.load` accepts an `f32` mask; `bad_mask_rejected` requires `bool`. The scalar-`if` check is `code_generator.py`, not `semantic.py`.
