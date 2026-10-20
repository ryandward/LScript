import LScript.Check

/-!
# Soundness

`compile_sound`: if the compiler accepts a program, the module it emits runs without a SyntaxError
or a ReferenceError, and every name the program declares holds a value of its declared type: an
`Int` is a double that is exactly a safe integer, and a `String` is a string.
-/

namespace LScript

/-- A JavaScript value has an LScript type. -/
def ValOf : JS.Val → Ty → Prop
  | .num n, .int => JS.isSafe n = true
  | .str _, .str => True
  | _, _ => False

/-- The checker's names are the module's names, and each holds a value of its type. -/
def Agrees (ctx : Ctx) (env : List (String × JS.Val)) : Prop :=
  (∀ x, (lookup ctx.vals x).isSome = (lookup env x).isSome) ∧
  ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf v τ

theorem lookup_cons {α : Type} {k x : String} {v : α} {rest : List (String × α)} :
    lookup ((k, v) :: rest) x = if k = x then some v else lookup rest x := rfl

theorem agrees_empty : Agrees .empty [] :=
  ⟨fun _ => rfl, fun _ _ h => by simp [Ctx.empty, lookup] at h⟩

theorem agrees_cons {ctx env x t v} (h : Agrees ctx env) (hv : ValOf v t) :
    Agrees { ctx with vals := (x, t) :: ctx.vals } ((x, v) :: env) := by
  refine ⟨fun y => ?_, fun y τ hy => ?_⟩
  · simp only [lookup_cons]
    by_cases e : x = y
    · simp [e]
    · simp only [e, if_false]; exact h.1 y
  · simp only [lookup_cons] at hy ⊢
    by_cases e : x = y
    · simp only [e, if_true] at hy ⊢; cases hy; exact ⟨v, rfl, hv⟩
    · simp only [e, if_false] at hy ⊢; exact h.2 y τ hy

/-- What the checker says an expression's type is, the module's value for it has. -/
theorem typeOf_sound {ctx env e t} (h : typeOf ctx e = .ok t) (ha : Agrees ctx env) :
    ∃ v, JS.evalExpr env (emitExpr e) = .ok v ∧ ValOf v t := by
  cases e with
  | int n =>
    simp only [typeOf] at h
    by_cases hs : JS.isSafe n = true
    · simp only [hs, if_true] at h; cases h
      exact ⟨.num n, by simp [emitExpr, JS.evalExpr, hs], hs⟩
    · simp only [hs] at h; cases h
  | str s =>
    simp only [typeOf] at h
    by_cases hs : JS.validStr s = true
    · simp only [hs, if_true] at h; cases h
      exact ⟨.str s, by simp [emitExpr, JS.evalExpr, hs], trivial⟩
    · simp only [hs] at h; cases h
  | var x =>
    simp only [typeOf] at h
    cases hx : lookup ctx.vals x with
    | none => simp only [hx] at h; cases h
    | some τ =>
      simp only [hx] at h; cases h
      obtain ⟨v, hv, hvt⟩ := ha.2 x _ hx
      exact ⟨v, by simp [emitExpr, JS.evalExpr, hv], hvt⟩

/-- A type declaration leaves the values alone. -/
theorem checkDecl_type {ctx ctx' a rhs} (h : checkDecl ctx (.type a rhs) = .ok ctx') :
    ctx'.vals = ctx.vals := by
  simp only [checkDecl] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · cases h

/-- A value declaration the checker accepts: a JavaScript name, not declared before, whose value
    has the declared type. -/
theorem checkDecl_val {ctx ctx' x tn e} (h : checkDecl ctx (.val x tn e) = .ok ctx') :
    JS.validIdent x = true ∧ lookup ctx.vals x = none ∧
      ∃ t, typeOf ctx e = .ok t ∧ ctx' = { ctx with vals := (x, t) :: ctx.vals } := by
  simp only [checkDecl] at h
  by_cases hv : JS.validIdent x = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hl : lookup ctx.vals x with
    | some _ => simp [hl] at h
    | none =>
      simp only [hl, Option.isSome_none, Bool.false_eq_true, if_false] at h
      refine ⟨hv, rfl, ?_⟩
      cases hr : resolve ctx.types tn with
      | error _ => simp [hr] at h
      | ok t =>
        cases ht : typeOf ctx e with
        | error _ => simp [hr, ht] at h
        | ok t' =>
          simp only [hr, ht] at h
          by_cases he : t' = t
          · subst he; simp at h; exact ⟨t', rfl, h.symm⟩
          · simp [he] at h
  · simp [hv] at h

/-- The invariant carries through the program, declaration by declaration. -/
theorem checkFrom_sound : ∀ (p : Program) {ctx ctx' env}, checkFrom ctx p = .ok ctx' →
    Agrees ctx env → ∃ env', JS.runFrom env (emit p) = .ok env' ∧ Agrees ctx' env' := by
  intro p
  induction p with
  | nil =>
    intro ctx ctx' env h ha
    simp only [checkFrom] at h; cases h
    exact ⟨env, rfl, ha⟩
  | cons d ds ih =>
    intro ctx ctx' env h ha
    simp only [checkFrom] at h
    cases hd : checkDecl ctx d with
    | error _ => simp [hd] at h
    | ok ctx₁ =>
      simp only [hd] at h
      cases d with
      | type a rhs =>
        have hvals := checkDecl_type hd
        have ha₁ : Agrees ctx₁ env := by unfold Agrees; rw [hvals]; exact ha
        exact ih h ha₁
      | val x tn e =>
        obtain ⟨hvalid, hfresh, t, ht, rfl⟩ := checkDecl_val hd
        obtain ⟨v, hv, hvt⟩ := typeOf_sound ht ha
        have hnot : (lookup env x).isSome = false := by rw [← ha.1 x, hfresh]; rfl
        obtain ⟨env', hrun, ha'⟩ := ih h (agrees_cons (x := x) ha hvt)
        refine ⟨env', ?_, ha'⟩
        simp only [emit, JS.runFrom, hvalid, Bool.not_true, Bool.false_eq_true, if_false, hnot, hv]
        exact hrun

/-- **Soundness.** If the compiler accepts a program, the module it emits runs without an error,
    and every name the checker declared holds a value of its declared type. -/
theorem compile_sound {p : Program} {out : JS.Program} (h : compile p = .ok out) :
    ∃ ctx env, check p = .ok ctx ∧ JS.run out = .ok env ∧
      ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf v τ := by
  simp only [compile] at h
  cases hc : check p with
  | error _ => simp [hc] at h
  | ok ctx =>
    simp only [hc] at h; cases h
    obtain ⟨env, hrun, ha⟩ := checkFrom_sound p hc agrees_empty
    exact ⟨ctx, env, rfl, hrun, ha.2⟩

/-- The names the program declares as values. -/
def valNames : Program → List String
  | [] => []
  | .type .. :: ds => valNames ds
  | .val x _ _ :: ds => x :: valNames ds

/-- Every value the program declares is one the checker declared, so `compile_sound` covers every
    name in the source. -/
theorem checkFrom_declares : ∀ (p : Program) {ctx ctx'}, checkFrom ctx p = .ok ctx' →
    ∀ x, x ∈ valNames p → (lookup ctx'.vals x).isSome := by
  intro p
  induction p with
  | nil => intro _ _ _ x hx; simp [valNames] at hx
  | cons d ds ih =>
    intro ctx ctx' h x hx
    simp only [checkFrom] at h
    cases hd : checkDecl ctx d with
    | error _ => simp [hd] at h
    | ok ctx₁ =>
      simp only [hd] at h
      cases d with
      | type a rhs => exact ih h x (by simpa [valNames] using hx)
      | val y tn e =>
        simp only [valNames, List.mem_cons] at hx
        rcases hx with rfl | hx
        · -- declared here, and nothing later removes a name
          obtain ⟨_, _, t, _, rfl⟩ := checkDecl_val hd
          exact keeps ds h x (by simp [lookup_cons])
        · exact ih h x hx
where
  /-- Checking more declarations never forgets a value. -/
  keeps : ∀ (p : Program) {ctx ctx'}, checkFrom ctx p = .ok ctx' →
      ∀ x, (lookup ctx.vals x).isSome → (lookup ctx'.vals x).isSome := by
    intro p
    induction p with
    | nil => intro ctx ctx' h x hx; simp only [checkFrom] at h; cases h; exact hx
    | cons d ds ih =>
      intro ctx ctx' h x hx
      simp only [checkFrom] at h
      cases hd : checkDecl ctx d with
      | error _ => simp [hd] at h
      | ok ctx₁ =>
        simp only [hd] at h
        apply ih h x
        cases d with
        | type a rhs => rw [checkDecl_type hd]; exact hx
        | val y tn e =>
          obtain ⟨_, hfresh, t, _, rfl⟩ := checkDecl_val hd
          simp only [lookup_cons]
          by_cases e : y = x
          · simp [e]
          · simp only [e, if_false]; exact hx

#print axioms compile_sound
#print axioms checkFrom_declares

end LScript
