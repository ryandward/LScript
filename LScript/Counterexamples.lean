import LScript.Check
import LScript.Typing

/-!
# What each load-bearing check stops, proved by removing it

For every check `Check.lean` tags `load-bearing`, `counterexamples` holds one program. `test/checks.mjs`
removes the check in a copy of the repository and has Lean prove, by `decide`, that the compiler then
accepts the program and its output goes wrong: it fails in the model of V8, or a name holds a value
that isn't of its declared type. `wrong_refutes` turns that into the statement that soundness is false
for that compiler. In the real build it proves the opposite, `wrong p = false`, for the same program,
so each program is wrong only without its check.

This module doesn't depend on the proof of `compile_sound`, so it builds in a copy where that proof
no longer holds.
-/

namespace LScript

/-- `DataOf`, decided to a depth of `n` nested records. At depth 0 it gives up and says yes, so a
    `false` is always a real failure: `dataOfB_complete`. A function type has no data. -/
def dataOfB : Nat → Recs → JS.Val → Ty → Bool
  | 0, _, _, _ => true
  | _ + 1, _, .num n, .int => JS.isSafe n
  | _ + 1, _, .str _, .str => true
  | n + 1, recs, .obj fs frozen, .record r =>
    match recs.find r with
    | none => false
    | some tfs =>
      frozen && fs.all (fun p => (lookup tfs p.1).isSome) &&
      tfs.all (fun p =>
        match lookup fs p.1, lookup tfs p.1 with
        | some v, some τ => dataOfB n recs v τ
        | _, _ => false)
  | _ + 1, _, _, _ => false

/-- `JS.Data`, decided to a depth of `n` nested objects; at depth 0 it says yes. -/
def dataB : Nat → JS.Val → Bool
  | 0, _ => true
  | _ + 1, .num _ => true
  | _ + 1, .str _ => true
  | n + 1, .obj fs true => fs.all fun p =>
    match lookup fs p.1 with
    | some v => dataB n v
    | none => false
  | _ + 1, _ => false

/-- An input `JSON.parse` could return for an entry's input type, where one is easy to name. -/
def sampleFor : Ty → JS.Val
  | .int => .num 0
  | .str => .str ""
  | _ => .undef

/-- `ValOf`, as far as it can be decided: data by `dataOfB`; a function only as far as being a closure,
    since what it does with every argument can't be decided by running it; and an entry by running its
    parse on `undefined` and on one input of its input type, where running out of fuel is no verdict. -/
def valOfB (n : Nat) (recs : Recs) : JS.Val → Ty → Bool
  | v, .int => dataOfB n recs v .int
  | v, .str => dataOfB n recs v .str
  | v, .record r => dataOfB n recs v (.record r)
  | v, .fn _ _ => match v with
    | .clos _ _ _ => true
    | _ => false
  | v, .entry a r => match v with
    | .entryOf c =>
      (match JS.applyVal n c .undef with
       | .ok w => valOfB n recs w r && dataB n w
       | .error .outOfFuel => true
       | .error _ => false) &&
      (match JS.applyVal n c (sampleFor a) with
       | .ok w => valOfB n recs w r && dataB n w
       | .error .outOfFuel => true
       | .error _ => false)
    | _ => false

theorem dataOfB_complete {recs : Recs} {v τ} (h : DataOf recs v τ) : ∀ n, dataOfB n recs v τ = true := by
  induction h with
  | int hs => intro n; cases n <;> simp [dataOfB, hs]
  | str => intro n; cases n <;> simp [dataOfB]
  | obj hl hk hp ih =>
    rename_i fs r tfs
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [dataOfB, hl, Bool.and_eq_true, List.all_eq_true]
      refine ⟨⟨trivial, fun p hm => ?_⟩, fun p hm => ?_⟩
      · obtain ⟨l, w⟩ := p
        rw [← hk]; exact lookup_isSome_of_mem hm
      · obtain ⟨l, τ'⟩ := p
        have ht : (lookup tfs l).isSome = true := lookup_isSome_of_mem hm
        have hf : (lookup fs l).isSome = true := by rw [hk]; exact ht
        cases hfl : lookup fs l with
        | none => rw [hfl] at hf; cases hf
        | some w =>
          cases htl : lookup tfs l with
          | none => rw [htl] at ht; cases ht
          | some τ => exact ih l w τ hfl htl n

theorem dataB_complete {v} (h : JS.Data v) : ∀ n, dataB n v = true := by
  induction h with
  | num => intro n; cases n <;> rfl
  | str => intro n; cases n <;> rfl
  | obj hfs ih =>
    rename_i fs
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [dataB, List.all_eq_true]
      intro p hp
      have hs := lookup_isSome_of_mem hp
      cases hl : lookup fs p.1 with
      | none => rw [hl] at hs; cases hs
      | some w => exact ih p.1 w hl n

theorem sampleFor_json (a : Ty) : JS.IsJson (sampleFor a) ∨ sampleFor a = .undef := by
  cases a with
  | int => exact Or.inl (.int (by decide))
  | str => exact Or.inl .str
  | record _ => exact Or.inr rfl
  | fn _ _ => exact Or.inr rfl
  | entry _ _ => exact Or.inr rfl

theorem valOfB_complete {recs : Recs} : ∀ {v τ}, ValOf recs v τ → ∀ n, valOfB n recs v τ = true
  | _, .int, h, n => dataOfB_complete h n
  | _, .str, h, n => dataOfB_complete h n
  | _, .record _, h, n => dataOfB_complete h n
  | _, .fn _ _, h, _ => by
    simp only [ValOf] at h
    obtain ⟨cenv, x, body, rfl, _⟩ := h
    rfl
  | _, .entry a r, h, n => by
    simp only [ValOf] at h
    obtain ⟨c, rfl, hc⟩ := h
    have key : ∀ j, (JS.IsJson j ∨ j = .undef) →
        (match JS.applyVal n c j with
         | .ok w => valOfB n recs w r && dataB n w
         | .error .outOfFuel => true
         | .error _ => false) = true := by
      intro j hj
      obtain ⟨n', w, hw, hwr, hwd⟩ := hc j hj
      cases happ : JS.applyVal n c j with
      | ok w' =>
        have h₁ := JS.applyVal_mono happ (by simp) (max n n') (Nat.le_max_left _ _)
        rw [JS.applyVal_mono hw (by simp) (max n n') (Nat.le_max_right _ _)] at h₁
        cases h₁
        simp [valOfB_complete hwr n, dataB_complete hwd n]
      | error e =>
        by_cases he : e = .outOfFuel
        · subst he; rfl
        · have h₁ := JS.applyVal_mono happ (by simpa using he) (max n n') (Nat.le_max_left _ _)
          rw [JS.applyVal_mono hw (by simp) (max n n') (Nat.le_max_right _ _)] at h₁
          cases h₁
    simp only [valOfB, Bool.and_eq_true]
    exact ⟨key _ (Or.inr rfl), key _ (sampleFor_json a)⟩

/-- What `compile_sound` concludes for a program the compiler accepts. -/
def Conclusion (p : Program) (out : JS.Program) : Prop :=
  ∃ ctx env, check p = .ok (ctx, out) ∧ (∃ n, JS.run n out = .ok env) ∧
    (∀ x τ, ctx.vals.find x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ) ∧
    ∀ d ∈ out, d.exported = true → ∃ v, lookup env d.name = some v ∧ JS.Exportable v

/-- The fuel `wrong` runs a module with. Running out is no verdict: more fuel might finish it. -/
def wrongFuel : Nat := 100

/-- The compiler accepts `p`, and its output fails in the model of V8, or a name holds a value that
    isn't of its declared type. -/
def wrong (p : Program) : Bool :=
  match check p with
  | .error _ => false
  | .ok (ctx, out) =>
    match JS.run wrongFuel out with
    | .error .outOfFuel => false
    | .error _ => true
    | .ok env => out.any fun d =>
      match ctx.vals.find d.name, lookup env d.name with
      | some τ, some v => !valOfB 100 ctx.recs v τ
      | some _, none => true
      | none, _ => false

/-- A wrong program refutes soundness, for whatever checker built it. -/
theorem wrong_refutes {p : Program} (hw : wrong p = true) :
    ¬ ∀ {p : Program} {out : JS.Program}, compile p = .ok out → Conclusion p out := by
  intro hsound
  unfold wrong at hw
  cases hc : check p with
  | error _ => simp [hc] at hw
  | ok res =>
    obtain ⟨ctx, out⟩ := res
    simp only [hc] at hw
    have hcomp : compile p = .ok out := by simp [compile, hc]
    obtain ⟨ctx', env, hc', ⟨n, hrun⟩, hall, -⟩ := hsound hcomp
    rw [hc] at hc'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc'
    obtain ⟨rfl, -⟩ := hc'
    -- Both runs agree at the larger fuel, unless the one `wrong` made ran out.
    have hbig := JS.run_mono hrun (by simp) (max n wrongFuel) (Nat.le_max_left _ _)
    cases hr : JS.run wrongFuel out with
    | error e =>
      rw [hr] at hw
      by_cases he : e = .outOfFuel
      · subst he; simp at hw
      · have := JS.run_mono hr (by simpa using he) (max n wrongFuel) (Nat.le_max_right _ _)
        rw [hbig] at this; cases this
    | ok env' =>
    have := JS.run_mono hr (by simp) (max n wrongFuel) (Nat.le_max_right _ _)
    rw [hbig] at this; cases this
    rw [hr] at hw
    simp only [List.any_eq_true] at hw
    obtain ⟨d, _, hbad⟩ := hw
    cases hl : ctx.vals.find d.name with
    | none => simp [hl] at hbad
    | some τ =>
      obtain ⟨v, hv, hvt⟩ := hall d.name τ hl
      simp only [hl, hv] at hbad
      have := valOfB_complete hvt 100
      simp [this] at hbad

def user : Decl := .record "User" [("name", .str), ("age", .int)]
def ann : Decl := .val "ann" (.named "User") (.record [("name", .str "Ann"), ("age", .int 42)])

/-- One counterexample per load-bearing check, by the check's code. -/
def counterexamples : List (String × Program) :=
  [("int-safe", [.val "big" .int (.atom (.int 9007199254740993))]),
   ("string-printable", [.val "s" .str (.atom (.str "a\\b"))]),
   ("field-declared", [user, .val "a" (.named "User")
      (.record [("name", .str "A"), ("age", .int 1), ("admin", .int 1)])]),
   ("field-type", [user, .val "a" (.named "User") (.record [("name", .str "A"), ("age", .str "old")])]),
   ("atom-type", [.val "x" .int (.atom (.str "ten"))]),
   ("read-type", [user, ann, .val "age" .int (.path "ann" ["name"])]),
   ("literal-record", [.val "x" .int (.record [])]),
   ("literal-distinct", [user, .val "a" (.named "User")
      (.record [("name", .str "A"), ("age", .int 1), ("age", .int 2)])]),
   ("literal-complete", [user, .val "a" (.named "User") (.record [("name", .str "A")])]),
   ("update-type", [user, .record "Pet" [("name", .str)], .val "rex" (.named "Pet") (.record [("name", .str "Rex")]),
      .val "u" (.named "User") (.update "rex" [])]),
   ("update-record", [.val "n" .int (.atom (.int 1)), .val "m" .int (.update "n" [])]),
   ("record-fresh", [.record "R" [("a", .int)], .val "x" (.named "R") (.record [("a", .int 1)]),
      .record "R" [("b", .str)], .val "y" .str (.path "x" ["b"])]),
   ("record-labels", [.record "P" [("__proto__", .int)], .val "p" (.named "P") (.record [("__proto__", .int 1)])]),
   ("val-ident", [.val "class" .int (.atom (.int 1))]),
   ("val-fresh", [.val "a" .int (.atom (.int 1)), .val "a" .int (.atom (.int 2))]),
   ("record-data", [.alias "F" (.fn .int .int), .record "R" [("f", .named "F")],
      .val "id" (.named "F") (.lam "x" (.atom (.var "x"))), .val "r" (.named "R") (.record [("f", .var "id")])]),
   ("lambda-type", [.val "x" .int (.lam "y" (.atom (.int 1)))]),
   ("param-ident", [.val "f" (.fn .int .int) (.lam "class" (.atom (.int 1)))]),
   ("call-type", [.val "n" .int (.atom (.int 1)), .val "m" .int (.app "n" (.int 1) [])]),
   ("entry-then", [.val "id" (.fn .int .int) (.lam "x" (.atom (.var "x"))), .entry "then" (.fn .int .int) "id" (.int 0)]),
   ("entry-type", [.val "f0" (.fn .int .int) (.lam "x" (.atom (.var "x"))),
      .val "konst" (.fn .int (.fn .int .int)) (.lam "x" (.atom (.var "f0"))),
      .entry "h" (.fn .int (.fn .int .int)) "konst" (.var "f0")]),
   ("entry-ok-type", [.val "n" .int (.atom (.int 1)), .entry "h" (.fn .int .int) "n" (.int 0)]),
   ("entry-fail-type", [.val "id" (.fn .int .int) (.lam "x" (.atom (.var "x"))), .entry "h" (.fn .int .int) "id" (.str "x")])]

def counterexample (name : String) : Program := (lookup counterexamples name).getD []

end LScript
