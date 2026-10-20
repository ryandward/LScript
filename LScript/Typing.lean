import LScript.JS

/-!
# What it means for a JavaScript value to have an LScript type

`ValOf` is the property `compile_sound` proves of every name the program declares. It lives apart from
the proof so that a build in which the proof no longer holds can still state it, which is what
`Counterexamples.lean` and `test/checks.mjs` do.
-/

namespace LScript

abbrev Recs := List (String × List (String × Ty))

/-- A JavaScript value has an LScript type. A record's object is frozen and has exactly the declared
    fields. -/
inductive ValOf (recs : Recs) : JS.Val → Ty → Prop where
  | int {n} : JS.isSafe n = true → ValOf recs (.num n) .int
  | str {s} : ValOf recs (.str s) .str
  | obj {fs r tfs} : lookup recs r = some tfs →
      (∀ l, (lookup fs l).isSome = (lookup tfs l).isSome) →
      (∀ l v τ, lookup fs l = some v → lookup tfs l = some τ → ValOf recs v τ) →
      ValOf recs (.obj fs true) (.record r)

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

theorem ValOf.mono {recs recs' : Recs} (hr : ∀ r tfs, lookup recs r = some tfs → lookup recs' r = some tfs)
    {v τ} (h : ValOf recs v τ) : ValOf recs' v τ := by
  induction h with
  | int hs => exact .int hs
  | str => exact .str
  | obj hl hk _ ih => exact .obj (hr _ _ hl) hk (fun l v τ h1 h2 => ih l v τ h1 h2)

end LScript
