# Small-step semantics of the TLA core-mode fragment

Date: 2026-10-29. The normative definition is the Lean development in this directory (`TAS/Basic.lean`, `TAS/Typing.lean`, `TAS/Step.lean`, `TAS/Examples.lean`, `TAS/Safety.lean`). This note records what those files say.

TAS models the cube and vector fragment of TLA: which core a name was born in, which memory space a buffer lives in, and the copy directions used by the mixed cube-then-vector kernel. A buffer is one abstract integer cell. `mmad` checks that its operands sit in L1 and L0C on the cube core and then finishes; it does not multiply matrices. `copy` moves that one cell. Loops, vector lanes, tensor layouts, and the compilation pipeline are outside this proof.

## Syntax

Two cores and four spaces:

| TAS | TLA |
|---|---|
| `Core.vec` | `with tla.scope.simd()` (`core_mode` `"vector"`) |
| `Core.cube` | `with tla.scope.cube()` (`core_mode` `"cube"`) |
| `Space.gm`, `.ub`, `.l1`, `.l0c` | GM, UB, L1, L0C |

Types are `scalar`, `reg k` (a name assigned inside core `k`), and `buf s` (a buffer in space `s`). Values carry the same tag plus one `Int`. `valTy` drops the integer.

Expressions: `val`, `var`, `add` (scalars), `splat` (scalar to a register of the current core), `vadd` (two registers of the current core), `vld` (the UB cell into a vector register). Commands: `skip`, `assign`, `seq`, `scope k`, `block k`, `vst`, `copy`, `mmad`. A source program uses `scope`. The machine introduces `block` when `scope` steps. `block` is the runtime frame of that core.

| TAS | TLA op |
|---|---|
| `splat` | `vfull` / `vsplat` |
| `vld` | `simd.vlds` from UB |
| `vadd` | `simd.vadd` |
| `vst` | `simd.vsts` into UB |
| `mmad` | `cube.mmad` with A and B in L1 and the accumulator in L0C |
| `copy` of GM to L1 inside cube | `tla.copy` into L1 (`nd2nz`) |
| `copy` of L0C to UB inside cube | fixpipe |
| `copy` of L0C to GM inside cube | cube store |
| `copy` of GM to UB, or UB to GM, outside either core | the loads and stores around the scopes |

Names are `Nat`. Contexts and environments are association lists; `lookup` takes the first match, and `update` conses a new binding, so a later assignment hides the earlier one.

## Typing

`regOk none k` is true: a register may be read outside either core. `regOk (some k') k` is true when `k'` and `k` are the same core. `tyOk` applies `regOk` to register types and accepts scalars and buffers in every core. This is the same birth rule as the TLA scope checker: a name assigned in `tla.scope.cube` is refused inside `tla.scope.simd`, and the reverse, while a name assigned outside both scopes stays usable in either.

`infer` and `check` return `Option`. The expression rules:

- A value is well typed when `tyOk` accepts `valTy`.
- A variable is well typed when its context binding is accepted by `tyOk`.
- `add` requires two scalars.
- `splat` requires a surrounding core and a scalar, and produces `reg` of that core.
- `vadd` requires a surrounding core `k` and two registers of `k`.
- `vld` requires the vector core and a UB buffer, and produces `reg vec`.

`check` is flow-sensitive. It returns the context after the command.

- `skip` returns the same context.
- `assign x e` updates `x` to the type of `e`.
- `seq` types the second command in the context produced by the first.
- `scope k body` and `block k body` both type `body` at `some k`.
- `vst` requires the vector core, a UB buffer, and a vector register. The context is unchanged; the store changes the cell at runtime.
- `copy` requires `copyOk`. The accepted directions are cube GM→L1, cube L0C→UB, cube L0C→GM, and, outside either core, GM→UB and UB→GM.
- `mmad` requires the cube core, two L1 buffers, and an L0C buffer.

`models env Γ` says every typed name has a value of that type.

## Small steps

`stepE` steps an expression and leaves the environment alone. `step` steps a command. Both are deterministic and partial: a stuck configuration is `none`.

- A variable loads its value when `tyOk` accepts that value in the current core.
- Two scalar values add. `splat` of a scalar in core `k` becomes `reg k`. Two registers of the current core `vadd`. `vld` of a UB cell on the vector core becomes a vector register holding that cell.
- `assign` of a value conses the binding and becomes `skip`. Otherwise the expression steps.
- `seq skip c` becomes `c`. Otherwise the first command steps under the sequence.
- `scope k body` becomes `block k body` in the same environment.
- `block k skip` becomes `skip`, back at the outer core. Otherwise the body steps at `some k`.
- `vst` of a vector register into a UB buffer on the vector core conses that cell and becomes `skip`.
- `copy` conses the destination buffer with the source cell when `copyOk` accepts the direction.
- `mmad`, once the spaces and the cube core match, becomes `skip` and does not write the accumulator.

`Steps here` is the reflexive-transitive closure of `step` at one fixed outer core. Inner cores travel inside `block`.

## Theorems

All of these are proved in `TAS/Safety.lean`. `lake build` checks them.

| Theorem | Statement |
|---|---|
| `scope_isolation` | A register of core `k` has no type in core `k'` when the cores differ. |
| `tyOk_reg` | If a register of core `k'` is accepted in core `k`, then `k = k'`. |
| `splat_birth` | `splat` in core `k` is born as `reg k`. |
| `vld_requires_ub` | A typed `vld` is on the vector core and reads a UB buffer. |
| `copy_respects_direction` | A typed `copy` satisfies `copyOk`. |
| `mmad_requires_cube` | A typed `mmad` is on the cube core, with L1, L1, and L0C. |
| `expr_progress` | A typed expression is a value, or `stepE` returns a successor. |
| `expr_preservation` | That successor has the same type. The environment is unchanged. |
| `progress` | A typed command is `skip`, or `step` returns a successor. |
| `preservation` | The successor is typed, the new environment matches the new context, and the result context of the original command is unchanged. |
| `type_safety` | Every configuration reachable by `Steps` from a typed command is typed at that same result context. |

`preservation` is the reason an assignment inside one core cannot be read as a register of the other core after a step: the context carried across the step is the one `check` produced, and `tyOk` still refuses the other core.

## Examples

`TAS/Examples.lean` is the one-cell cut of `unittest/tla_ut/cube/gemm_bias.py`, plus the programs the scope rule rejects. Names: `aGm = 0`, `aL1 = 1`, `bGm = 2`, `bL1 = 3`, `cL0c = 4`, `cUb = 5`, `bias = 6`, `vreg = 7`, `cGm = 8`. The cube body copies GM to L1, runs `mmad`, and copies L0C to UB. The vector body splats a scalar, loads the UB cell, and stores the sum back to UB. The program then copies UB to GM outside either scope.

| Theorem | What `native_decide` or `rfl` checks |
|---|---|
| `gemm_bias_typed` | The mixed program type-checks. Buffers allocated outside either scope are used in both. |
| `cross_scope_rejected` | A register assigned in cube and read in vector is rejected. |
| `rebound_typed` | Assigning the name again inside the reading core drops the previous core's type. |
| `scalar_both_typed` | A scalar assigned outside both cores is readable in each. |
| `nested_cross_rejected` | A register born in an outer vector scope is rejected in an inner cube scope. |
| `gemm_bias_steps_into_cube` | The first step turns `scope cube` into `block cube` and leaves the environment in place. |

## What this development does not claim

The Python scope checker records only the birth core of a name. TAS also records scalar, register, and buffer, and the space of each buffer, so the memory operations have a type-safety theorem. A loop index would be an assignment in the core that contains the loop; loops are not in the calculus. The integer stored in a buffer is a carrier for `copy`, `vld`, and `vst`. It is not a tile, and the development does not prove the numeric result of a matrix product. Acceptance of TTIR, the adapter, or `bishengir` is the subject of `docs/staged-compilation-contracts-triton-ascend.md`.
