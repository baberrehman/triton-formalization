import TAS.Examples

/-
Birth-core walk transcribed from `scope_check.py` (`bind_name`, `_use`,
`check_stmt`). A core binding is recorded for every assignment inside
`cube` or `vector`, and cleared by an assignment outside either core.
A read fails only when the current core differs from that birth core.

TAS records a core only on register types. The two therefore agree on the
register programs in `TAS/Examples.lean`, and they differ when a scalar is
assigned inside a core: this walk rejects a later read from the other core,
and TAS accepts it.
-/
set_option autoImplicit false

namespace TAS

abbrev Births := List (Nat × Core)

def erase (x : Nat) : Births → Births
  | [] => []
  | (y, k) :: rest => if y = x then erase x rest else (y, k) :: erase x rest

/-- `bind_name`: inside a core, record `x`; outside, drop it. -/
def bindName (mode : Option Core) (x : Nat) (bs : Births) : Births :=
  match mode with
  | none => erase x bs
  | some k => (x, k) :: bs

def coreEq (k k' : Core) : Bool :=
  match k, k' with
  | .vec, .vec => true
  | .cube, .cube => true
  | _, _ => false

/-- `_use`: outside a core, allow; inside, reject a name born in the other core. -/
def useOk (mode : Option Core) (bs : Births) (x : Nat) : Bool :=
  match mode with
  | none => true
  | some k =>
      match lookup bs x with
      | none => true
      | some k' => coreEq k k'

def uses : Expr → List Nat
  | .val _ => []
  | .var x => [x]
  | .add e1 e2 => uses e1 ++ uses e2
  | .splat e => uses e
  | .vadd e1 e2 => uses e1 ++ uses e2
  | .vld e => uses e

def allUse (mode : Option Core) (bs : Births) (xs : List Nat) : Bool :=
  xs.all (useOk mode bs)

def scopeCmd (mode : Option Core) (bs : Births) : Cmd → Option Births
  | .skip => some bs
  | .assign x e =>
      if allUse mode bs (uses e) then some (bindName mode x bs) else none
  | .seq c1 c2 =>
      match scopeCmd mode bs c1 with
      | some bs1 => scopeCmd mode bs1 c2
      | none => none
  | .scope k body => scopeCmd (some k) bs body
  | .block k body => scopeCmd (some k) bs body
  | .vst b e =>
      if useOk mode bs b && allUse mode bs (uses e) then some bs else none
  | .copy src dst =>
      if useOk mode bs src && useOk mode bs dst then some bs else none
  | .mmad a b acc =>
      if useOk mode bs a && useOk mode bs b && useOk mode bs acc then some bs else none

/-- A read of a register born in the other core is rejected by the scope walk. -/
theorem cross_core_read_scope {k k' : Core} (h : ¬ k = k') :
    scopeCmd (some k) [(0, k')] (.assign 1 (.var 0)) = none := by
  cases k <;> cases k' <;> first
    | (exact absurd rfl h)
    | (unfold scopeCmd uses allUse useOk lookup coreEq; rfl)

/-- The same read is rejected by TAS, because `tyOk` refuses the other core. -/
theorem cross_core_read_tas {k k' : Core} (h : ¬ k = k') :
    check (some k) [(0, .reg k')] (.assign 1 (.var 0)) = none := by
  cases k <;> cases k' <;> first
    | (exact absurd rfl h)
    | (unfold check checkAssign infer inferVar tyOk regOk lookup; rfl)

theorem scope_gemm_bias_accepted : (scopeCmd none [] gemmBias).isSome = true := by
  native_decide

theorem scope_cross_rejected : scopeCmd none [] crossScope = none := by
  native_decide

theorem scope_rebound_accepted : (scopeCmd none [] rebound).isSome = true := by
  native_decide

theorem scope_scalar_both_accepted : (scopeCmd none [] scalarBoth).isSome = true := by
  native_decide

theorem scope_nested_cross_rejected : scopeCmd none [] nestedCross = none := by
  native_decide

/-- A scalar assigned inside cube is still a scalar for TAS, so vector code may read it. -/
def scalarInside : Cmd :=
  .seq (.scope .cube (.assign bias (.val (.scalar 1))))
       (.scope .vec (.assign vreg (.var bias)))

theorem scalar_inside_tas_accepted : (check none [] scalarInside).isSome = true := by
  native_decide

/-- The scope walk records that assignment as a cube birth and rejects the vector read. -/
theorem scalar_inside_scope_rejected : scopeCmd none [] scalarInside = none := by
  native_decide

end TAS
