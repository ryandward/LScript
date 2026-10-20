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

/-- `ValOf`, decided to a depth of `n` nested records. At depth 0 it gives up and says yes, so a `false`
    is always a real failure: `valOfB_complete`. -/
def valOfB : Nat → Recs → JS.Val → Ty → Bool
  | 0, _, _, _ => true
  | _ + 1, _, .num n, .int => JS.isSafe n
  | _ + 1, _, .str _, .str => true
  | n + 1, recs, .obj fs, .record r =>
    match lookup recs r with
    | none => false
    | some tfs =>
      fs.all (fun p => (lookup tfs p.1).isSome) &&
      tfs.all (fun p =>
        match lookup fs p.1, lookup tfs p.1 with
        | some v, some τ => valOfB n recs v τ
        | _, _ => false)
  | _ + 1, _, _, _ => false

theorem valOfB_complete {recs : Recs} {v τ} (h : ValOf recs v τ) : ∀ n, valOfB n recs v τ = true := by
  induction h with
  | int hs => intro n; cases n <;> simp [valOfB, hs]
  | str => intro n; cases n <;> simp [valOfB]
  | obj hl hk hp ih =>
    rename_i fs r tfs
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [valOfB, hl, Bool.and_eq_true, List.all_eq_true]
      refine ⟨fun p hm => ?_, fun p hm => ?_⟩
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

/-- What `compile_sound` concludes for a program the compiler accepts. -/
def Conclusion (p : Program) (out : JS.Program) : Prop :=
  ∃ ctx env, check p = .ok (ctx, out) ∧ JS.run out = .ok env ∧
    ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ

/-- The compiler accepts `p`, and its output fails in the model of V8, or a name holds a value that
    isn't of its declared type. -/
def wrong (p : Program) : Bool :=
  match check p with
  | .error _ => false
  | .ok (ctx, out) =>
    match JS.run out with
    | .error _ => true
    | .ok env => ctx.vals.any fun q =>
      match lookup ctx.vals q.1, lookup env q.1 with
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
    obtain ⟨ctx', env, hc', hrun, hall⟩ := hsound hcomp
    rw [hc] at hc'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc'
    obtain ⟨rfl, -⟩ := hc'
    rw [hrun] at hw
    simp only [List.any_eq_true] at hw
    obtain ⟨q, _, hbad⟩ := hw
    cases hl : lookup ctx.vals q.1 with
    | none => simp [hl] at hbad
    | some τ =>
      obtain ⟨v, hv, hvt⟩ := hall q.1 τ hl
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
   ("val-fresh", [.val "a" .int (.atom (.int 1)), .val "a" .int (.atom (.int 2))])]

def counterexample (name : String) : Program := (lookup counterexamples name).getD []

end LScript
