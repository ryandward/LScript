import LScript.Check

/-!
# Soundness

`compile_sound`: if the compiler accepts a program, the module it emits runs without an error in the
model of V8, and every name the program declares holds a value of its declared type. An `Int` is a
double that is exactly a safe integer, a `String` is a string, and a record is an object whose own
fields are exactly the record's declared fields, each holding a value of its declared type. So no
field read the checker accepts ever gives `undefined`.
-/

namespace LScript

abbrev Recs := List (String × List (String × Ty))

/-- A JavaScript value has an LScript type. A record's object has exactly the declared fields. -/
inductive ValOf (recs : Recs) : JS.Val → Ty → Prop where
  | int {n} : JS.isSafe n = true → ValOf recs (.num n) .int
  | str {s} : ValOf recs (.str s) .str
  | obj {fs r tfs} : lookup recs r = some tfs →
      (∀ l, (lookup fs l).isSome = (lookup tfs l).isSome) →
      (∀ l v τ, lookup fs l = some v → lookup tfs l = some τ → ValOf recs v τ) →
      ValOf recs (.obj fs) (.record r)

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

/-! ## The invariant -/

/-- The checker's names are the module's names, and each holds a value of its type. -/
def Agrees (ctx : Ctx) (env : List (String × JS.Val)) : Prop :=
  (∀ x, (lookup ctx.vals x).isSome = (lookup env x).isSome) ∧
  ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ

/-- Every record is a declared type name, so a fresh type name is a fresh record. -/
def RecsTyped (ctx : Ctx) : Prop := ∀ r, (lookup ctx.recs r).isSome → (lookup ctx.types r).isSome

theorem agrees_cons {ctx env x t v} (h : Agrees ctx env) (hv : ValOf ctx.recs v t) :
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

/-! ## Expressions -/

theorem inferAtom_sound {ctx env a t} (h : inferAtom ctx a = .ok t) (ha : Agrees ctx env) :
    ∃ v, JS.evalAtom env (emitAtom a) = .ok v ∧ ValOf ctx.recs v t := by
  cases a with
  | int n =>
    simp only [inferAtom] at h
    by_cases hs : JS.isSafe n = true
    · simp only [hs, if_true] at h; cases h
      exact ⟨.num n, by simp [emitAtom, JS.evalAtom, hs], .int hs⟩
    · simp only [hs] at h; cases h
  | str s =>
    simp only [inferAtom] at h
    by_cases hs : JS.validStr s = true
    · simp only [hs, if_true] at h; cases h
      exact ⟨.str s, by simp [emitAtom, JS.evalAtom, hs], .str⟩
    · simp only [hs] at h; cases h
  | var x =>
    simp only [inferAtom] at h
    cases hx : lookup ctx.vals x with
    | none => simp only [hx] at h; cases h
    | some τ =>
      simp only [hx] at h; cases h
      obtain ⟨v, hv, hvt⟩ := ha.2 x _ hx
      exact ⟨v, by simp [emitAtom, JS.evalAtom, hv, JS.readPath], hvt⟩

/-- Reading the fields a chain of types promises gives a value of the last type. -/
theorem fieldPath_sound {recs : Recs} : ∀ (ls : List String) {t t' v},
    fieldPath recs t ls = .ok t' → ValOf recs v t → ValOf recs (JS.readPath v ls) t' := by
  intro ls
  induction ls with
  | nil => intro t t' v h hv; simp only [fieldPath] at h; cases h; exact hv
  | cons l ls ih =>
    intro t t' v h hv
    cases t with
    | int => simp [fieldPath] at h
    | str => simp [fieldPath] at h
    | record r =>
      simp only [fieldPath] at h
      cases hr : lookup recs r with
      | none => simp [hr] at h
      | some tfs =>
        simp only [hr] at h
        cases hl : lookup tfs l with
        | none => simp [hl] at h
        | some t₁ =>
          simp only [hl] at h
          cases hv with
          | obj hr' hk hp =>
            rename_i fs tfs'
            rw [hr] at hr'; cases hr'
            have hs : (lookup fs l).isSome = true := by rw [hk l, hl]; rfl
            cases hf : lookup fs l with
            | none => rw [hf] at hs; cases hs
            | some w =>
              have hw := hp l w t₁ hf hl
              have : JS.readPath (.obj fs) (l :: ls) = JS.readPath w ls := by
                simp [JS.readPath, List.foldl, JS.readField, hf]
              rw [this]; exact ih h hw

theorem checkFields_spec {ctx r tfs} : ∀ (fs : List (String × Atom)), checkFields ctx r tfs fs = .ok () →
    ∀ l a, (l, a) ∈ fs → ∃ τ, lookup tfs l = some τ ∧ inferAtom ctx a = .ok τ := by
  intro fs
  induction fs with
  | nil => intro _ l a h; simp at h
  | cons p rest ih =>
    obtain ⟨l₀, a₀⟩ := p
    intro h l a hm
    simp only [checkFields] at h
    cases hl : lookup tfs l₀ with
    | none => simp [hl] at h
    | some τ =>
      cases ht : inferAtom ctx a₀ with
      | error _ => simp [hl, ht] at h
      | ok τ' =>
        simp only [hl, ht] at h
        by_cases e : τ' = τ
        · simp only [e, if_true] at h
          rcases List.mem_cons.mp hm with hm | hm
          · cases hm; exact ⟨τ, hl, by rw [ht, e]⟩
          · exact ih h l a hm
        · simp [e] at h

theorem evalFields_ok {env : List (String × JS.Val)} {Q : String → JS.Val → Prop} :
    ∀ (fs : List (String × JS.Atom)),
      (∀ l a, (l, a) ∈ fs → ∃ v, JS.evalAtom env a = .ok v ∧ Q l v) →
      ∃ vs, JS.evalFields env fs = .ok vs ∧ vs.map Prod.fst = fs.map Prod.fst ∧
        ∀ l v, lookup vs l = some v → Q l v := by
  intro fs
  induction fs with
  | nil => intro _; exact ⟨[], rfl, rfl, fun l v h => by simp [lookup] at h⟩
  | cons p rest ih =>
    obtain ⟨l₀, a₀⟩ := p
    intro h
    obtain ⟨v₀, hv₀, hq₀⟩ := h l₀ a₀ List.mem_cons_self
    obtain ⟨vs, hvs, hkeys, hq⟩ := ih (fun l a hm => h l a (List.mem_cons_of_mem _ hm))
    refine ⟨(l₀, v₀) :: vs, by simp [JS.evalFields, hv₀, hvs], by simp [hkeys], fun l v hl => ?_⟩
    simp only [lookup_cons] at hl
    by_cases e : l₀ = l
    · simp only [e, if_true] at hl; cases hl; subst e; exact hq₀
    · simp only [e, if_false] at hl; exact hq l v hl

theorem labelsOk_spec {ls : List String} (h : labelsOk ls = true) :
    ls.all JS.validLabel = true ∧ ls.Nodup := by
  simp only [labelsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem evalExpr_obj {env : List (String × JS.Val)} {fs : List (String × JS.Atom)} {vs}
    (hv : (fs.map Prod.fst).all JS.validLabel = true) (hn : (fs.map Prod.fst).Nodup)
    (he : JS.evalFields env fs = .ok vs) : JS.evalExpr env (.obj fs) = .ok (.obj vs) := by
  simp [JS.evalExpr, hv, hn, he]

/-- What the checker accepts against a type, the emitted JavaScript evaluates to a value of it. -/
theorem checkExpr_sound {ctx env e τ je} (h : checkExpr ctx e τ = .ok je) (ha : Agrees ctx env) :
    ∃ v, JS.evalExpr env je = .ok v ∧ ValOf ctx.recs v τ := by
  cases e with
  | atom a =>
    simp only [checkExpr] at h
    cases hi : inferAtom ctx a with
    | error _ => simp [hi] at h
    | ok t =>
      simp only [hi] at h
      by_cases e : t = τ
      · simp only [e, if_true] at h; cases h; subst e
        obtain ⟨v, hv, hvt⟩ := inferAtom_sound hi ha
        exact ⟨v, by simpa [JS.evalExpr] using hv, hvt⟩
      · simp [e] at h
  | path x ls =>
    simp only [checkExpr] at h
    cases hx : lookup ctx.vals x with
    | none => simp [hx] at h
    | some t =>
      simp only [hx] at h
      cases hp : fieldPath ctx.recs t ls with
      | error _ => simp [hp] at h
      | ok t' =>
        simp only [hp] at h
        by_cases e : t' = τ
        · simp only [e, if_true] at h; cases h; subst e
          obtain ⟨v, hv, hvt⟩ := ha.2 x t hx
          exact ⟨JS.readPath v ls, by simp [JS.evalExpr, JS.evalAtom, hv], fieldPath_sound ls hp hvt⟩
        · simp [e] at h
  | record fs =>
    simp only [checkExpr] at h
    cases τ with
    | int => simp at h
    | str => simp at h
    | record r =>
      simp only at h
      cases hr : lookup ctx.recs r with
      | none => simp [hr] at h
      | some tfs =>
        simp only [hr] at h
        by_cases hlab : labelsOk (fs.map Prod.fst) = true
        · simp only [hlab, Bool.not_true, Bool.false_eq_true, if_false] at h
          cases hc : checkFields ctx r tfs fs with
          | error _ => simp [hc] at h
          | ok u =>
            cases u
            simp only [hc] at h
            cases hfind : tfs.find? (fun p => (lookup fs p.1).isNone) with
            | some p => simp [hfind] at h
            | none =>
              simp only [hfind] at h; cases h
              have hspec := checkFields_spec fs hc
              obtain ⟨hvalid, hnodup⟩ := labelsOk_spec hlab
              let efs := fs.map fun (p : String × Atom) => (p.1, emitAtom p.2)
              have hkeys₁ : efs.map Prod.fst = fs.map Prod.fst := by simp [efs]
              obtain ⟨vs, hvs, hkeys, hq⟩ := evalFields_ok (env := env)
                (Q := fun l v => ∃ τ', lookup tfs l = some τ' ∧ ValOf ctx.recs v τ') efs
                (fun l ea hm => by
                  obtain ⟨⟨l', a⟩, hm', he⟩ := List.mem_map.mp hm
                  simp only [Prod.mk.injEq] at he
                  obtain ⟨he₁, he₂⟩ := he
                  subst he₁; subst he₂
                  obtain ⟨τ', hτ', hi⟩ := hspec l' a hm'
                  obtain ⟨v, hv, hvt⟩ := inferAtom_sound hi ha
                  exact ⟨v, hv, τ', hτ', hvt⟩)
              refine ⟨.obj vs, ?_, .obj hr (fun l => ?_) (fun l v τ' hv hτ' => ?_)⟩
              · have hv' : (efs.map Prod.fst).all JS.validLabel = true := by rw [hkeys₁]; exact hvalid
                have hn' : (efs.map Prod.fst).Nodup := by rw [hkeys₁]; exact hnodup
                exact evalExpr_obj hv' hn' hvs
              · rw [lookup_isSome_keys (hkeys.trans hkeys₁)]
                cases hf : lookup fs l with
                | some a =>
                  obtain ⟨τ', hτ', _⟩ := hspec l a (lookup_mem hf)
                  rw [hτ']; rfl
                | none =>
                  cases ht : lookup tfs l with
                  | none => rfl
                  | some τ' =>
                    have := List.find?_eq_none.mp hfind (l, τ') (lookup_mem ht)
                    simp [hf] at this
              · obtain ⟨τ'', h₁, h₂⟩ := hq l v hv
                rw [hτ'] at h₁; cases h₁; exact h₂
        · simp [hlab] at h
  | update x fs =>
    simp only [checkExpr] at h
    cases hx : lookup ctx.vals x with
    | none => simp [hx] at h
    | some t =>
      cases t with
      | int => simp [hx] at h
      | str => simp [hx] at h
      | record r =>
        simp only [hx] at h
        by_cases hτ : Ty.record r = τ
        · subst hτ
          simp only [ne_eq, not_true_eq_false, if_false] at h
          cases hr : lookup ctx.recs r with
          | none => simp [hr] at h
          | some tfs =>
            simp only [hr] at h
            by_cases hlab : labelsOk (fs.map Prod.fst) = true
            · by_cases htlab : labelsOk (tfs.map Prod.fst) = true
              · simp only [hlab, htlab, Bool.not_true, Bool.false_eq_true, if_false] at h
                cases hc : checkFields ctx r tfs fs with
                | error _ => simp [hc] at h
                | ok u =>
                  cases u
                  simp only [hc] at h; cases h
                  have hspec := checkFields_spec fs hc
                  obtain ⟨htvalid, htnodup⟩ := labelsOk_spec htlab
                  obtain ⟨vx, hvx, hvxt⟩ := ha.2 x _ hx
                  cases hvxt with
                  | obj hr' hk hp =>
                    rename_i xs tfs'
                    rw [hr] at hr'; cases hr'
                    let pick : String × Ty → String × JS.Atom := fun p =>
                      (p.1, match lookup fs p.1 with
                            | some a => emitAtom a
                            | none => .path x [p.1])
                    let efs := tfs.map pick
                    have hkeys₁ : efs.map Prod.fst = tfs.map Prod.fst := by simp [efs, pick]
                    obtain ⟨vs, hvs, hkeys, hq⟩ := evalFields_ok (env := env)
                      (Q := fun l v => ∃ τ', lookup tfs l = some τ' ∧ ValOf ctx.recs v τ') efs
                      (fun l ea hm => by
                        obtain ⟨⟨l', τl⟩, hm', he⟩ := List.mem_map.mp hm
                        simp only [pick, Prod.mk.injEq] at he; obtain ⟨rfl, he⟩ := he
                        have hτl : lookup tfs l' = some τl := lookup_of_mem htnodup hm'
                        cases hf : lookup fs l' with
                        | some a =>
                          rw [hf] at he; subst he
                          obtain ⟨τ', hτ', hi⟩ := hspec l' a (lookup_mem hf)
                          rw [hτl] at hτ'; cases hτ'
                          obtain ⟨v, hv, hvt⟩ := inferAtom_sound hi ha
                          exact ⟨v, hv, τl, hτl, hvt⟩
                        | none =>
                          rw [hf] at he; subst he
                          have hs : (lookup xs l').isSome = true := by rw [hk l', hτl]; rfl
                          cases hxl : lookup xs l' with
                          | none => rw [hxl] at hs; cases hs
                          | some w =>
                            refine ⟨w, ?_, τl, hτl, hp l' w τl hxl hτl⟩
                            simp [JS.evalAtom, hvx, JS.readPath, List.foldl, JS.readField, hxl])
                    refine ⟨.obj vs, ?_, .obj hr (fun l => ?_) (fun l v τ' hv hτ' => ?_)⟩
                    · have hv' : (efs.map Prod.fst).all JS.validLabel = true := by rw [hkeys₁]; exact htvalid
                      have hn' : (efs.map Prod.fst).Nodup := by rw [hkeys₁]; exact htnodup
                      exact evalExpr_obj hv' hn' hvs
                    · exact lookup_isSome_keys (hkeys.trans hkeys₁)
                    · obtain ⟨τ'', h₁, h₂⟩ := hq l v hv
                      rw [hτ'] at h₁; cases h₁; exact h₂
              · simp [hlab, htlab] at h
            · simp [hlab] at h
        · simp [hτ] at h

/-! ## Declarations -/

theorem checkDecl_alias {ctx a rhs ctx' jd} (h : checkDecl ctx (.alias a rhs) = .ok (ctx', jd)) :
    jd = none ∧ ctx'.vals = ctx.vals ∧ ctx'.recs = ctx.recs ∧ ∃ t, ctx'.types = (a, t) :: ctx.types := by
  simp only [checkDecl] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl, rfl, _, rfl⟩
      · cases h

theorem checkDecl_record {ctx r fields ctx' jd} (h : checkDecl ctx (.record r fields) = .ok (ctx', jd)) :
    jd = none ∧ ctx'.vals = ctx.vals ∧ lookup ctx.types r = none ∧
      ∃ tfs, ctx'.recs = (r, tfs) :: ctx.recs ∧ ctx'.types = (r, .record r) :: ctx.types := by
  simp only [checkDecl] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hfresh
      split at h
      · cases h
      · split at h
        · cases h
          refine ⟨rfl, rfl, ?_, _, rfl, rfl⟩
          cases hl : lookup ctx.types r with
          | none => rfl
          | some _ => simp [hl] at hfresh
        · cases h

theorem checkDecl_val {ctx x tn e ctx' jd} (h : checkDecl ctx (.val x tn e) = .ok (ctx', jd)) :
    JS.validIdent x = true ∧ lookup ctx.vals x = none ∧ ctx'.recs = ctx.recs ∧ ctx'.types = ctx.types ∧
      ∃ τ je, checkExpr ctx e τ = .ok je ∧ ctx'.vals = (x, τ) :: ctx.vals ∧ jd = some ⟨x, je⟩ := by
  simp only [checkDecl] at h
  by_cases hv : JS.validIdent x = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, if_false] at h
    cases hl : lookup ctx.vals x with
    | some _ => simp [hl] at h
    | none =>
      simp only [hl, Option.isSome_none, Bool.false_eq_true, if_false] at h
      cases hr : resolve ctx.types tn with
      | error _ => simp [hr] at h
      | ok τ =>
        simp only [hr] at h
        cases hc : checkExpr ctx e τ with
        | error _ => simp [hc] at h
        | ok je =>
          simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hv, rfl, rfl, rfl, τ, je, hc, rfl, rfl⟩
  · simp [hv] at h

/-- The invariant carries through the program, declaration by declaration. -/
theorem checkFrom_sound : ∀ (p : Program) {ctx ctx' js env}, checkFrom ctx p = .ok (ctx', js) →
    Agrees ctx env → RecsTyped ctx →
    ∃ env', JS.runFrom env js = .ok env' ∧ Agrees ctx' env' ∧ RecsTyped ctx' := by
  intro p
  induction p with
  | nil =>
    intro ctx ctx' js env h ha hr
    simp only [checkFrom, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨env, rfl, ha, hr⟩
  | cons d ds ih =>
    intro ctx ctx' js env h ha hr
    simp only [checkFrom] at h
    cases hd : checkDecl ctx d with
    | error _ => simp [hd] at h
    | ok res =>
      obtain ⟨ctx₁, jd⟩ := res
      simp only [hd] at h
      cases hrest : checkFrom ctx₁ ds with
      | error _ => simp [hrest] at h
      | ok res' =>
        obtain ⟨ctx₂, js'⟩ := res'
        simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases d with
        | alias a rhs =>
          obtain ⟨rfl, hvals, hrecs, t, htypes⟩ := checkDecl_alias hd
          have ha₁ : Agrees ctx₁ env := by unfold Agrees; rw [hvals, hrecs]; exact ha
          have hr₁ : RecsTyped ctx₁ := by
            intro r' hs
            rw [hrecs] at hs; rw [htypes, lookup_cons]
            by_cases e : a = r'
            · simp [e]
            · simp only [e, if_false]; exact hr r' hs
          exact ih hrest ha₁ hr₁
        | record r fields =>
          obtain ⟨rfl, hvals, hfresh, tfs, hrecs, htypes⟩ := checkDecl_record hd
          have hnorec : lookup ctx.recs r = none := by
            cases hl : lookup ctx.recs r with
            | none => rfl
            | some _ => have := hr r (by rw [hl]; rfl); rw [hfresh] at this; cases this
          have hmono : ∀ r' tfs', lookup ctx.recs r' = some tfs' → lookup ctx₁.recs r' = some tfs' := by
            intro r' tfs' hl
            rw [hrecs, lookup_cons]
            have : r ≠ r' := fun e => by subst e; rw [hnorec] at hl; cases hl
            simp only [this, if_false]; exact hl
          have ha₁ : Agrees ctx₁ env := by
            refine ⟨fun y => by rw [hvals]; exact ha.1 y, fun y τ hy => ?_⟩
            rw [hvals] at hy
            obtain ⟨v, hv, hvt⟩ := ha.2 y τ hy
            exact ⟨v, hv, ValOf.mono hmono hvt⟩
          have hr₁ : RecsTyped ctx₁ := by
            intro r' hs
            rw [htypes, lookup_cons]
            by_cases e : r = r'
            · simp [e]
            · simp only [e, if_false]
              rw [hrecs, lookup_cons] at hs; simp only [e, if_false] at hs
              exact hr r' hs
          exact ih hrest ha₁ hr₁
        | val x tn e =>
          obtain ⟨hvalid, hfreshv, hrecs, htypes, τ, je, hc, hvals, rfl⟩ := checkDecl_val hd
          obtain ⟨v, hv, hvt⟩ := checkExpr_sound hc ha
          have hnot : (lookup env x).isSome = false := by rw [← ha.1 x, hfreshv]; rfl
          have ha₁ : Agrees ctx₁ ((x, v) :: env) := by
            have := agrees_cons (x := x) ha hvt
            unfold Agrees at this ⊢
            rw [hvals, hrecs]; exact this
          have hr₁ : RecsTyped ctx₁ := by unfold RecsTyped; rw [hrecs, htypes]; exact hr
          obtain ⟨env', hrun, ha', hr'⟩ := ih hrest ha₁ hr₁
          refine ⟨env', ?_, ha', hr'⟩
          simp only [JS.runFrom, hvalid, Bool.not_true, Bool.false_eq_true, if_false, hnot, hv]
          exact hrun

/-- **Soundness.** If the compiler accepts a program, the module it emits runs without an error, and
    every name the checker declared holds a value of its declared type. -/
theorem compile_sound {p : Program} {out : JS.Program} (h : compile p = .ok out) :
    ∃ ctx env, check p = .ok (ctx, out) ∧ JS.run out = .ok env ∧
      ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ := by
  simp only [compile] at h
  cases hc : check p with
  | error _ => simp [hc] at h
  | ok res =>
    obtain ⟨ctx, js⟩ := res
    simp only [hc, Except.ok.injEq] at h; subst h
    obtain ⟨env, hrun, ha, _⟩ := checkFrom_sound p (env := []) hc
      ⟨fun _ => rfl, fun _ _ h => by simp [Ctx.empty, lookup] at h⟩
      (fun _ h => by simp [Ctx.empty, lookup] at h)
    exact ⟨ctx, env, rfl, hrun, ha.2⟩

/-- The names the program declares as values. -/
def valNames : Program → List String
  | [] => []
  | .val x _ _ :: ds => x :: valNames ds
  | _ :: ds => valNames ds

/-- Checking more declarations never forgets a value. -/
theorem checkFrom_keeps : ∀ (p : Program) {ctx ctx' js}, checkFrom ctx p = .ok (ctx', js) →
    ∀ x, (lookup ctx.vals x).isSome → (lookup ctx'.vals x).isSome := by
  intro p
  induction p with
  | nil =>
    intro ctx ctx' js h x hx
    simp only [checkFrom, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hx
  | cons d ds ih =>
    intro ctx ctx' js h x hx
    simp only [checkFrom] at h
    cases hd : checkDecl ctx d with
    | error _ => simp [hd] at h
    | ok res =>
      obtain ⟨ctx₁, jd⟩ := res
      simp only [hd] at h
      cases hrest : checkFrom ctx₁ ds with
      | error _ => simp [hrest] at h
      | ok res' =>
        obtain ⟨ctx₂, js'⟩ := res'
        simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply ih hrest x
        cases d with
        | alias a rhs => rw [(checkDecl_alias hd).2.1]; exact hx
        | record r fields => rw [(checkDecl_record hd).2.1]; exact hx
        | val y tn e =>
          obtain ⟨_, _, _, _, τ, _, _, hvals, _⟩ := checkDecl_val hd
          rw [hvals, lookup_cons]
          by_cases e : y = x
          · simp [e]
          · simp only [e, if_false]; exact hx

/-- Every value the program declares is one the checker declared, so `compile_sound` covers every
    name in the source. -/
theorem checkFrom_declares : ∀ (p : Program) {ctx ctx' js}, checkFrom ctx p = .ok (ctx', js) →
    ∀ x, x ∈ valNames p → (lookup ctx'.vals x).isSome := by
  intro p
  induction p with
  | nil => intro _ _ _ _ x hx; simp [valNames] at hx
  | cons d ds ih =>
    intro ctx ctx' js h x hx
    simp only [checkFrom] at h
    cases hd : checkDecl ctx d with
    | error _ => simp [hd] at h
    | ok res =>
      obtain ⟨ctx₁, jd⟩ := res
      simp only [hd] at h
      cases hrest : checkFrom ctx₁ ds with
      | error _ => simp [hrest] at h
      | ok res' =>
        obtain ⟨ctx₂, js'⟩ := res'
        simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases d with
        | alias a rhs => exact ih hrest x (by simpa [valNames] using hx)
        | record r fields => exact ih hrest x (by simpa [valNames] using hx)
        | val y tn e =>
          simp only [valNames, List.mem_cons] at hx
          rcases hx with rfl | hx
          · obtain ⟨_, _, _, _, τ, _, _, hvals, _⟩ := checkDecl_val hd
            exact checkFrom_keeps ds hrest x (by rw [hvals]; simp [lookup_cons])
          · exact ih hrest x hx

#print axioms compile_sound
#print axioms checkFrom_declares

end LScript
