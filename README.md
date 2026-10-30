# Formal semantics for Triton and for the TLA core-mode fragment

Date: 2026-10-30.

Two Lean developments live here. Both are checked with Lean 4.19.0 (`lean-toolchain` pins `leanprover/lean4:v4.19.0`).

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd docs/triton-formalization
lake build
```

**Triton** (`Triton/`) is a small-step semantics of the `tl.*` language. The proved property is the class of checks in `python/triton/language/semantic.py`: dtype, rank, broadcast, mask, and a scalar condition on `if`. `triton-semantics.md` is the human-readable account. `lake build` elaborates `expr_progress`, `expr_preservation`, `progress`, `preservation`, and `type_safety` in `Triton/Safety.lean`. There is no `sorry`.

**TAS** (`TAS/`) is a core calculus for the cube and vector fragment of Triton Language for Ascend. `semantics.md` states that development. It does not describe the `tl.*` surface, and the Triton development does not replace it.

Pipeline acceptance between Triton-Ascend stages is a separate note: `docs/staged-compilation-contracts-triton-ascend.md`.
