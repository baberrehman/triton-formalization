import TAS.Typing

/-
Small-step rules. Expressions reduce one redex at a time. A `scope` steps to
a `block`, which is the frame that runs the body at that core and then leaves it.
-/
set_option autoImplicit false

namespace TAS

def stepE (here : Option Core) (env : Env) : Expr → Option Expr
  | .val _ => none
  | .var x =>
      match lookup env x with
      | some v =>
          match tyOk here (valTy v) with
          | true => some (.val v)
          | false => none
      | none => none
  | .add e1 e2 =>
      match e1, e2 with
      | .val (.scalar n), .val (.scalar m) => some (.val (.scalar (n + m)))
      | .val _, _ =>
          match stepE here env e2 with
          | some e2' => some (.add e1 e2')
          | none => none
      | _, _ =>
          match stepE here env e1 with
          | some e1' => some (.add e1' e2)
          | none => none
  | .splat e =>
      match e with
      | .val (.scalar n) =>
          match here with
          | some k => some (.val (.reg k n))
          | none => none
      | .val _ => none
      | _ =>
          match stepE here env e with
          | some e' => some (.splat e')
          | none => none
  | .vadd e1 e2 =>
      match e1, e2 with
      | .val (.reg k1 n), .val (.reg k2 m) =>
          match here with
          | some k =>
              match k == k1 && k == k2 with
              | true => some (.val (.reg k (n + m)))
              | false => none
          | none => none
      | .val _, _ =>
          match stepE here env e2 with
          | some e2' => some (.vadd e1 e2')
          | none => none
      | _, _ =>
          match stepE here env e1 with
          | some e1' => some (.vadd e1' e2)
          | none => none
  | .vld e =>
      match e with
      | .val (.buf .ub n) =>
          match here with
          | some .vec => some (.val (.reg .vec n))
          | _ => none
      | .val _ => none
      | _ =>
          match stepE here env e with
          | some e' => some (.vld e')
          | none => none

def step (here : Option Core) (env : Env) : Cmd → Option (Env × Cmd)
  | .skip => none
  | .assign x e =>
      match e with
      | .val v => some ((x, v) :: env, .skip)
      | _ =>
          match stepE here env e with
          | some e' => some (env, .assign x e')
          | none => none
  | .seq c1 c2 =>
      match c1 with
      | .skip => some (env, c2)
      | _ =>
          match step here env c1 with
          | some (env', c1') => some (env', .seq c1' c2)
          | none => none
  | .scope k body => some (env, .block k body)
  | .block k body =>
      match body with
      | .skip => some (env, .skip)
      | _ =>
          match step (some k) env body with
          | some (env', body') => some (env', .block k body')
          | none => none
  | .vst b e =>
      match e with
      | .val v =>
          match here, lookup env b, v with
          | some .vec, some (.buf .ub _), .reg .vec n =>
              some ((b, .buf .ub n) :: env, .skip)
          | _, _, _ => none
      | _ =>
          match stepE here env e with
          | some e' => some (env, .vst b e')
          | none => none
  | .copy src dst =>
      match lookup env src, lookup env dst with
      | some (.buf s n), some (.buf d _) =>
          match copyOk here s d with
          | true => some ((dst, .buf d n) :: env, .skip)
          | false => none
      | _, _ => none
  | .mmad a b acc =>
      match here, lookup env a, lookup env b, lookup env acc with
      | some .cube, some (.buf .l1 _), some (.buf .l1 _), some (.buf .l0c _) =>
          some (env, .skip)
      | _, _, _, _ => none

/-- Reachable in zero or more top-level steps. The outer core stays fixed;
inner cores are carried by `block`. -/
inductive Steps (here : Option Core) : Env → Cmd → Env → Cmd → Prop where
  | refl (env : Env) (c : Cmd) : Steps here env c env c
  | tail (env : Env) (c : Cmd) (env1 : Env) (c1 : Cmd) (env2 : Env) (c2 : Cmd) :
      step here env c = some (env1, c1) →
      Steps here env1 c1 env2 c2 →
      Steps here env c env2 c2

end TAS
