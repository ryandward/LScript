import LScript.JS

/-!
# What it means for a JavaScript value to have an LScript type

`ValOf` is the property `compile_sound` proves of every name the program declares. It lives apart from
the proof so that a build in which the proof no longer holds can still state it, which is what
`Counterexamples.lean` and `test/checks.mjs` do.
-/

namespace LScript

abbrev Recs := Scope (List (String × Ty))

/-- A JavaScript value is data of an LScript type: a safe integer, a string, or a frozen object with
    exactly the record's declared fields, each holding data of its declared type. A function type has
    no data, so a record can't hold a function. -/
inductive DataOf (recs : Recs) : JS.Val → Ty → Prop where
  | int {n} : JS.isSafe n = true → DataOf recs (.num n) .int
  | str {s} : DataOf recs (.str s) .str
  | obj {fs r tfs} : recs.find r = some tfs →
      (∀ l, (lookup fs l).isSome = (lookup tfs l).isSome) →
      (∀ l v τ, lookup fs l = some v → lookup tfs l = some τ → DataOf recs v τ) →
      DataOf recs (.obj fs true) (.record r)

/-- A JavaScript value has an LScript type. Data is `DataOf`. A function is a closure that, given any
    value of its parameter type, finishes at some fuel with a value of its result type: it neither
    throws nor runs forever. An entry holds a parse function that, given anything `JSON.parse` returns,
    or `undefined`, finishes with data of the entry's result type. -/
def ValOf (recs : Recs) : JS.Val → Ty → Prop
  | v, .int => DataOf recs v .int
  | v, .str => DataOf recs v .str
  | v, .record r => DataOf recs v (.record r)
  | v, .fn a b => ∃ cenv x body, v = .clos cenv x body ∧
      ∀ w, ValOf recs w a → ∃ n r, JS.evalExpr n ((x, w) :: cenv) body = .ok r ∧ ValOf recs r b
  | v, .entry _ b => ∃ c, v = .entryOf c ∧
      ∀ j, (JS.IsJson j ∨ j = .undef) → ∃ n r, JS.applyVal n c j = .ok r ∧ ValOf recs r b ∧ JS.Data r

/-! ## Association lists -/

theorem lookup_cons {α : Type} {k x : String} {v : α} {rest : List (String × α)} :
    lookup ((k, v) :: rest) x = if k = x then some v else lookup rest x := rfl

theorem lookup_mem {α : Type} : ∀ {xs : List (String × α)} {l v}, lookup xs l = some v → (l, v) ∈ xs
  | [], _, _, h => by simp [lookup] at h
  | (k, w) :: rest, l, v, h => by
    simp only [lookup_cons] at h
    by_cases e : k = l
    · simp only [e, if_true] at h; cases h; subst e; exact List.mem_cons_self
    · simp only [e, if_false] at h; exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_isSome_of_mem {α : Type} : ∀ {xs : List (String × α)} {l v}, (l, v) ∈ xs → (lookup xs l).isSome
  | [], _, _, h => by simp at h
  | (k, w) :: rest, l, v, h => by
    simp only [lookup_cons]
    by_cases e : k = l
    · simp [e]
    · simp only [e, if_false]
      rcases List.mem_cons.mp h with h | h
      · cases h; exact absurd rfl e
      · exact lookup_isSome_of_mem h

theorem lookup_of_mem {α : Type} : ∀ {xs : List (String × α)} {l v},
    (xs.map Prod.fst).Nodup → (l, v) ∈ xs → lookup xs l = some v
  | [], _, _, _, h => by simp at h
  | (k, w) :: rest, l, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [lookup_cons]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have hk : k ≠ l := fun e => hn.1 (by subst e; exact List.mem_map.mpr ⟨(k, v), h, rfl⟩)
      simp only [hk, if_false]; exact lookup_of_mem hn.2 h

theorem lookup_isSome_keys {α β : Type} : ∀ {xs : List (String × α)} {ys : List (String × β)} {l},
    xs.map Prod.fst = ys.map Prod.fst → (lookup xs l).isSome = (lookup ys l).isSome
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | (k, v) :: xs, (k', w) :: ys, l, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hk, hrest⟩ := h
    simp only [lookup_cons]
    subst hk
    by_cases e : k = l
    · simp [e]
    · simp only [e, if_false]; exact lookup_isSome_keys hrest

theorem DataOf.mono {recs recs' : Recs} (hr : ∀ r tfs, recs.find r = some tfs → recs'.find r = some tfs)
    {v τ} (h : DataOf recs v τ) : DataOf recs' v τ := by
  induction h with
  | int hs => exact .int hs
  | str => exact .str
  | obj hl hk _ ih => exact .obj (hr _ _ hl) hk (fun l v τ h1 h2 => ih l v τ h1 h2)

theorem DataOf.valOf {recs v t} (h : DataOf recs v t) : ValOf recs v t := by
  cases t with
  | int => exact h
  | str => exact h
  | record r => exact h
  | fn a b => cases h
  | entry a b => cases h

theorem ValOf.dataOf {recs v t} (hd : isData t = true) (h : ValOf recs v t) : DataOf recs v t := by
  cases t with
  | int => exact h
  | str => exact h
  | record r => exact h
  | fn a b => simp [isData] at hd
  | entry a b => simp [isData] at hd

end LScript
