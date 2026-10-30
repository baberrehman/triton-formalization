# TAS: a small-step semantics for the TLA core-mode fragment

Date: 2026-10-29.

TAS (Triton-Ascend Small) is a core calculus for the cube and vector fragment of Triton Language for Ascend. The Lean sources in this directory are the definition. They are checked with Lean 4.19.0 (`lean-toolchain` pins `leanprover/lean4:v4.19.0`).

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd docs/triton-formalization
lake build
```

`lake build` elaborates every theorem in `TAS/Safety.lean`, including `expr_progress`, `expr_preservation`, `progress`, `preservation`, and `type_safety`. There is no `sorry`.

`semantics.md` states the syntax, the typing rules, the small-step rules, the theorem names, and the correspondence with `tla.scope.simd`, `tla.scope.cube`, and the memory ops used by `gemm_bias`. Pipeline acceptance between Triton-Ascend stages is a separate note: `docs/staged-compilation-contracts-triton-ascend.md`.
