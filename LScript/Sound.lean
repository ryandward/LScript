import LScript.Check
import LScript.Typing
import LScript.Counterexamples

/-!
# Soundness

`compile_sound`: if the compiler accepts a program, the module it emits runs without an error in the
model of V8, and every name the program declares holds a value of its declared type. An `Int` is a
double that is exactly a safe integer, a `String` is a string, and a record is an object whose own
fields are exactly the record's declared fields, each holding a value of its declared type. So no
field read the checker accepts ever gives `undefined`.
-/

namespace LScript

/-! ## The invariant -/

/-- The checker's names are the module's names, and each holds a value of its type. -/
def Agrees (ctx : Ctx) (env : List (String × JS.Val)) : Prop :=
  (∀ x, (lookup ctx.vals x).isSome = (lookup env x).isSome) ∧
  ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ

/-- A record type that is in scope has its fields. -/
def TyOk (recs : Recs) : Ty → Prop
  | .record r => (lookup recs r).isSome
  | _ => True

theorem TyOk.mono {recs recs' : Recs} (hr : ∀ r tfs, lookup recs r = some tfs → lookup recs' r = some tfs) :
    ∀ {t}, TyOk recs t → TyOk recs' t
  | .int, _ => trivial
  | .str, _ => trivial
  | .record r, h => by
    simp only [TyOk] at h ⊢
    cases hl : lookup recs r with
    | none => rw [hl] at h; cases h
    | some tfs => rw [hr r tfs hl]; rfl

/-- What the declarations so far established, proved once where each is declared: every record is a
    declared type name, so a fresh type name is a fresh record; every record's labels are ones the
    emitted object can carry; and every type in scope refers only to declared records. -/
structure DeclsOk (ctx : Ctx) : Prop where
  recsTyped : ∀ r, (lookup ctx.recs r).isSome → (lookup ctx.types r).isSome
  labels : ∀ r tfs, lookup ctx.recs r = some tfs → labelsOk (tfs.map Prod.fst) = true
  types : ∀ a t, lookup ctx.types a = some t → TyOk ctx.recs t
  vals : ∀ x t, lookup ctx.vals x = some t → TyOk ctx.recs t
  fields : ∀ r tfs, lookup ctx.recs r = some tfs → ∀ l t, lookup tfs l = some t → TyOk ctx.recs t

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
    split at h
    · cases h
    · rename_i hs'
      cases h
      have hs : JS.isSafe n = true := by simpa using hs'
      exact ⟨.num n, by simp [emitAtom, JS.evalAtom, hs], .int hs⟩
  | str s =>
    simp only [inferAtom] at h
    split at h
    · cases h
    · rename_i hs'
      cases h
      have hs : JS.validStr s = true := by simpa using hs'
      exact ⟨.str s, by simp [emitAtom, JS.evalAtom, hs], .str⟩
  | var x =>
    simp only [inferAtom] at h
    cases hx : lookup ctx.vals x with
    | none => simp only [hx] at h; cases h
    | some τ =>
      simp only [hx] at h; cases h
      obtain ⟨v, hv, hvt⟩ := ha.2 x _ hx
      exact ⟨v, by simp [emitAtom, JS.evalAtom, hv, JS.readPath], hvt⟩

/-- Reading the fields a chain of types promises gives a value of the last type. -/
theorem fieldPath_sound {ctx : Ctx} : ∀ (ls : List String) {t t' v},
    fieldPath ctx t ls = .ok t' → ValOf ctx.recs v t → ValOf ctx.recs (JS.readPath v ls) t' := by
  intro ls
  induction ls with
  | nil => intro t t' v h hv; simp only [fieldPath] at h; cases h; exact hv
  | cons l ls ih =>
    intro t t' v h hv
    simp only [fieldPath] at h
    cases t with
    | int => simp [fieldsOfTy, lookup] at h
    | str => simp [fieldsOfTy, lookup] at h
    | record r =>
      cases hv with
      | obj hr hk hp =>
        rename_i fs tfs
        have hf : fieldsOfTy ctx (.record r) = tfs := by simp [fieldsOfTy, fieldsOf, hr]
        rw [hf] at h
        cases hl : lookup tfs l with
        | none => simp [hl] at h
        | some t₁ =>
          simp only [hl] at h
          have hs : (lookup fs l).isSome = true := by rw [hk l, hl]; rfl
          cases hfl : lookup fs l with
          | none => rw [hfl] at hs; cases hs
          | some w =>
            have hw := hp l w t₁ hfl hl
            have : JS.readPath (.obj fs) (l :: ls) = JS.readPath w ls := by
              simp [JS.readPath, List.foldl, JS.readField, hfl]
            rw [this]; exact ih h hw

theorem checkFields_spec {ctx t} : ∀ (fs : List (String × Atom)), checkFields ctx t fs = .ok () →
    ∀ l a, (l, a) ∈ fs → ∃ τ, lookup (fieldsOfTy ctx t) l = some τ ∧ inferAtom ctx a = .ok τ := by
  intro fs
  induction fs with
  | nil => intro _ l a h; simp at h
  | cons p rest ih =>
    obtain ⟨l₀, a₀⟩ := p
    intro h l a hm
    simp only [checkFields] at h
    cases hl : lookup (fieldsOfTy ctx t) l₀ with
    | none => simp [hl] at h
    | some τ =>
      simp only [hl] at h
      cases ht : inferAtom ctx a₀ with
      | error _ => simp [ht] at h
      | ok τ' =>
        simp only [ht] at h
        split at h
        · cases h
        · rename_i e'
          have e : τ' = τ := by simpa using e'
          rcases List.mem_cons.mp hm with hm | hm
          · cases hm; exact ⟨τ, hl, by rw [ht, e]⟩
          · exact ih h l a hm

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

theorem lookup_key {α : Type} {xs : List (String × α)} {l v} (h : lookup xs l = some v) : l ∈ xs.map Prod.fst :=
  List.mem_map.mpr ⟨(l, v), lookup_mem h, rfl⟩

/-- A record type in scope has its fields: the record it names was declared. -/
theorem record_declared {recs : Recs} {r} (h : TyOk recs (.record r)) : ∃ tfs, lookup recs r = some tfs := by
  simp only [TyOk] at h
  cases hl : lookup recs r with
  | none => rw [hl] at h; cases h
  | some tfs => exact ⟨tfs, rfl⟩

/-- What the checker accepts against a type in scope, the emitted JavaScript evaluates to a value
    of it. -/
theorem checkExpr_sound {ctx env e τ je} (h : checkExpr ctx e τ = .ok je) (ha : Agrees ctx env)
    (hd : DeclsOk ctx) (hτ : TyOk ctx.recs τ) :
    ∃ v, JS.evalExpr env je = .ok v ∧ ValOf ctx.recs v τ := by
  cases e with
  | atom a =>
    simp only [checkExpr] at h
    cases hi : inferAtom ctx a with
    | error _ => simp [hi] at h
    | ok t =>
      simp only [hi] at h
      split at h
      · cases h
      · rename_i e'
        have e : t = τ := by simpa using e'
        cases h; subst e
        obtain ⟨v, hv, hvt⟩ := inferAtom_sound hi ha
        exact ⟨v, by simpa [JS.evalExpr] using hv, hvt⟩
  | path x ls =>
    simp only [checkExpr] at h
    cases hx : lookup ctx.vals x with
    | none => simp [hx] at h
    | some t =>
      simp only [hx] at h
      cases hp : fieldPath ctx t ls with
      | error _ => simp [hp] at h
      | ok t' =>
        simp only [hp] at h
        split at h
        · cases h
        · rename_i e'
          have e : t' = τ := by simpa using e'
          cases h; subst e
          obtain ⟨v, hv, hvt⟩ := ha.2 x t hx
          exact ⟨JS.readPath v ls, by simp [JS.evalExpr, JS.evalAtom, hv], fieldPath_sound ls hp hvt⟩
  | record fs =>
    simp only [checkExpr] at h
    split at h
    · cases h
    · rename_i hrec'
      have hrec : isRecord τ = true := by simpa using hrec'
      cases τ with
      | int => simp [isRecord] at hrec
      | str => simp [isRecord] at hrec
      | record r =>
      obtain ⟨tfs, hr⟩ := record_declared hτ
      have hf : fieldsOfTy ctx (.record r) = tfs := by simp [fieldsOfTy, fieldsOf, hr]
      obtain ⟨htvalid, _⟩ := labelsOk_spec (hd.labels r tfs hr)
      split at h
      · cases h
      · rename_i hnd'
        have hnd : (fs.map Prod.fst).Nodup := by simpa using hnd'
        cases hc : checkFields ctx (.record r) fs with
        | error _ => simp [hc] at h
        | ok u =>
          cases u
          simp only [hc] at h
          rw [hf] at h
          split at h
          · cases h
          · rename_i hall'
            have hall : (tfs.all fun p => (lookup fs p.1).isSome) = true := by
              cases hb : (tfs.all fun p => (lookup fs p.1).isSome) with
              | true => rfl
              | false => rw [hb] at hall'; simp at hall'
            cases h
            have hspec := checkFields_spec fs hc
            rw [hf] at hspec
            let efs := fs.map fun (p : String × Atom) => (p.1, emitAtom p.2)
            have hkeys₁ : efs.map Prod.fst = fs.map Prod.fst := by simp [efs]
            have hvalid : (fs.map Prod.fst).all JS.validLabel = true := by
              refine List.all_eq_true.mpr fun l hl => ?_
              obtain ⟨⟨l', a⟩, hm, he⟩ := List.mem_map.mp hl
              simp only at he; subst he
              obtain ⟨τ', hτ', _⟩ := hspec l' a hm
              exact List.all_eq_true.mp htvalid l' (lookup_key hτ')
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
              have hn' : (efs.map Prod.fst).Nodup := by rw [hkeys₁]; exact hnd
              exact evalExpr_obj hv' hn' hvs
            · rw [lookup_isSome_keys (hkeys.trans hkeys₁)]
              cases hfl : lookup fs l with
              | some a =>
                obtain ⟨τ', hτ', _⟩ := hspec l a (lookup_mem hfl)
                rw [hτ']; rfl
              | none =>
                cases ht : lookup tfs l with
                | none => rfl
                | some τ' =>
                  have := List.all_eq_true.mp hall (l, τ') (lookup_mem ht)
                  simp [hfl] at this
            · obtain ⟨τ'', h₁, h₂⟩ := hq l v hv
              rw [hτ'] at h₁; cases h₁; exact h₂
  | update x fs =>
    simp only [checkExpr] at h
    cases hx : lookup ctx.vals x with
    | none => simp [hx] at h
    | some t =>
      simp only [hx] at h
      split at h
      · cases h
      · rename_i hrec'
        have hrec : isRecord t = true := by simpa using hrec'
        cases t with
        | int => simp [isRecord] at hrec
        | str => simp [isRecord] at hrec
        | record r =>
        split at h
        · cases h
        · rename_i hτr'
          have hτr : Ty.record r = τ := by simpa using hτr'
          subst hτr
          split at h
          · cases h
          · cases hc : checkFields ctx (.record r) fs with
            | error _ => simp [hc] at h
            | ok u =>
              cases u
              simp only [hc] at h; cases h
              have hspec := checkFields_spec fs hc
              obtain ⟨vx, hvx, hvxt⟩ := ha.2 x _ hx
              cases hvxt with
              | obj hr hk hp =>
                rename_i xs tfs
                have hf : fieldsOfTy ctx (.record r) = tfs := by simp [fieldsOfTy, fieldsOf, hr]
                rw [hf] at hspec; rw [hf]
                obtain ⟨htvalid, htnodup⟩ := labelsOk_spec (hd.labels r tfs hr)
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
                    cases hfl : lookup fs l' with
                    | some a =>
                      rw [hfl] at he; subst he
                      obtain ⟨τ', hτ', hi⟩ := hspec l' a (lookup_mem hfl)
                      rw [hτl] at hτ'; cases hτ'
                      obtain ⟨v, hv, hvt⟩ := inferAtom_sound hi ha
                      exact ⟨v, hv, τl, hτl, hvt⟩
                    | none =>
                      rw [hfl] at he; subst he
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


/-! ## Declarations -/

theorem resolve_tyOk {ctx tn t} (hd : DeclsOk ctx) (h : resolve ctx.types tn = .ok t) : TyOk ctx.recs t := by
  cases tn with
  | int => simp only [resolve] at h; cases h; trivial
  | str => simp only [resolve] at h; cases h; trivial
  | named a =>
    simp only [resolve] at h
    cases hl : lookup ctx.types a with
    | none => simp [hl] at h
    | some t' => simp only [hl] at h; cases h; exact hd.types a _ hl

theorem resolveFields_spec {types : List (String × Ty)} : ∀ (fs : List (String × TyName)) {tfs},
    resolveFields types fs = .ok tfs →
      tfs.map Prod.fst = fs.map Prod.fst ∧ ∀ p ∈ tfs, ∃ tn, resolve types tn = .ok p.2 := by
  intro fs
  induction fs with
  | nil => intro tfs h; simp only [resolveFields] at h; cases h; exact ⟨rfl, fun p hp => by simp at hp⟩
  | cons q rest ih =>
    obtain ⟨l, tn⟩ := q
    intro tfs h
    simp only [resolveFields] at h
    cases hr : resolve types tn with
    | error _ => simp [hr] at h
    | ok t =>
      cases hrest : resolveFields types rest with
      | error _ => simp [hr, hrest] at h
      | ok ts =>
        simp only [hr, hrest, Except.ok.injEq] at h; subst h
        obtain ⟨hkeys, hres⟩ := ih hrest
        refine ⟨by simp [hkeys], fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with hp | hp
        · subst hp; exact ⟨tn, hr⟩
        · exact hres p hp

theorem checkDecl_alias {ctx a rhs ctx' jd} (h : checkDecl ctx (.alias a rhs) = .ok (ctx', jd)) :
    jd = none ∧ ctx'.vals = ctx.vals ∧ ctx'.recs = ctx.recs ∧
      ∃ t, resolve ctx.types rhs = .ok t ∧ ctx'.types = (a, t) :: ctx.types := by
  simp only [checkDecl] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases hr : resolve ctx.types rhs with
      | error _ => simp [hr] at h
      | ok t =>
        simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, rfl, t, rfl, rfl⟩

theorem checkDecl_record {ctx r fields ctx' jd} (h : checkDecl ctx (.record r fields) = .ok (ctx', jd)) :
    jd = none ∧ ctx'.vals = ctx.vals ∧ lookup ctx.types r = none ∧ labelsOk (fields.map Prod.fst) = true ∧
      ∃ tfs, resolveFields ctx.types fields = .ok tfs ∧ ctx'.recs = (r, tfs) :: ctx.recs ∧
        ctx'.types = (r, .record r) :: ctx.types := by
  simp only [checkDecl] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hfresh
      split at h
      · cases h
      · rename_i hlab
        cases hr : resolveFields ctx.types fields with
        | error _ => simp [hr] at h
        | ok tfs =>
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨rfl, rfl, ?_, by simpa using hlab, tfs, rfl, rfl, rfl⟩
          cases hl : lookup ctx.types r with
          | none => rfl
          | some _ => simp [hl] at hfresh

theorem checkDecl_val {ctx x tn e ctx' jd} (h : checkDecl ctx (.val x tn e) = .ok (ctx', jd)) :
    JS.validIdent x = true ∧ lookup ctx.vals x = none ∧ ctx'.recs = ctx.recs ∧ ctx'.types = ctx.types ∧
      ∃ τ je, resolve ctx.types tn = .ok τ ∧ checkExpr ctx e τ = .ok je ∧
        ctx'.vals = (x, τ) :: ctx.vals ∧ jd = some ⟨x, je⟩ := by
  simp only [checkDecl] at h
  split at h
  · cases h
  · rename_i hv
    split at h
    · cases h
    · rename_i hfresh
      cases hr : resolve ctx.types tn with
      | error _ => simp [hr] at h
      | ok τ =>
        simp only [hr] at h
        cases hc : checkExpr ctx e τ with
        | error _ => simp [hc] at h
        | ok je =>
          simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by simpa using hv, ?_, rfl, rfl, τ, je, rfl, hc, rfl, rfl⟩
          cases hl : lookup ctx.vals x with
          | none => rfl
          | some _ => simp [hl] at hfresh

/-- The invariant carries through the program, declaration by declaration. -/
theorem checkFrom_sound : ∀ (p : Program) {ctx ctx' js env}, checkFrom ctx p = .ok (ctx', js) →
    Agrees ctx env → DeclsOk ctx →
    ∃ env', JS.runFrom env js = .ok env' ∧ Agrees ctx' env' ∧ DeclsOk ctx' := by
  intro p
  induction p with
  | nil =>
    intro ctx ctx' js env h ha hd
    simp only [checkFrom, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨env, rfl, ha, hd⟩
  | cons d ds ih =>
    intro ctx ctx' js env h ha hd
    simp only [checkFrom] at h
    cases hdec : checkDecl ctx d with
    | error _ => simp [hdec] at h
    | ok res =>
      obtain ⟨ctx₁, jd⟩ := res
      simp only [hdec] at h
      cases hrest : checkFrom ctx₁ ds with
      | error _ => simp [hrest] at h
      | ok res' =>
        obtain ⟨ctx₂, js'⟩ := res'
        simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases d with
        | alias a rhs =>
          obtain ⟨rfl, hvals, hrecs, t, hres, htypes⟩ := checkDecl_alias hdec
          have ht : TyOk ctx.recs t := resolve_tyOk hd hres
          have ha₁ : Agrees ctx₁ env := by unfold Agrees; rw [hvals, hrecs]; exact ha
          refine ih hrest ha₁ ⟨fun r' hs => ?_, fun r' tfs' h' => ?_, fun a' t' h' => ?_, fun y t' h' => ?_,
            fun r' tfs' h' => ?_⟩
          · rw [hrecs] at hs; rw [htypes, lookup_cons]
            by_cases e : a = r'
            · simp [e]
            · simp only [e, if_false]; exact hd.recsTyped r' hs
          · rw [hrecs] at h'; exact hd.labels r' tfs' h'
          · rw [hrecs]; rw [htypes, lookup_cons] at h'
            by_cases e : a = a'
            · simp only [e, if_true] at h'; cases h'; exact ht
            · simp only [e, if_false] at h'; exact hd.types a' t' h'
          · rw [hrecs]; rw [hvals] at h'; exact hd.vals y t' h'
          · rw [hrecs] at h' ⊢; exact hd.fields r' tfs' h'
        | record r fields =>
          obtain ⟨rfl, hvals, hfresh, hlab, tfs, hres, hrecs, htypes⟩ := checkDecl_record hdec
          have hnorec : lookup ctx.recs r = none := by
            cases hl : lookup ctx.recs r with
            | none => rfl
            | some _ => have := hd.recsTyped r (by rw [hl]; rfl); rw [hfresh] at this; cases this
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
          obtain ⟨hkeys, hresolved⟩ := resolveFields_spec fields hres
          refine ih hrest ha₁ ⟨fun r' hs => ?_, fun r' tfs' h' => ?_, fun a t' h' => ?_, fun y t' h' => ?_,
            fun r' tfs' h' l t' ht' => ?_⟩
          · rw [htypes, lookup_cons]
            by_cases e : r = r'
            · simp [e]
            · simp only [e, if_false]
              rw [hrecs, lookup_cons] at hs; simp only [e, if_false] at hs
              exact hd.recsTyped r' hs
          · rw [hrecs, lookup_cons] at h'
            by_cases e : r = r'
            · simp only [e, if_true] at h'; cases h'; rw [hkeys]; exact hlab
            · simp only [e, if_false] at h'; exact hd.labels r' tfs' h'
          · rw [htypes, lookup_cons] at h'
            by_cases e : r = a
            · simp only [e, if_true] at h'; cases h'; subst e
              simp only [TyOk]; rw [hrecs, lookup_cons]; simp
            · simp only [e, if_false] at h'; exact TyOk.mono hmono (hd.types a t' h')
          · rw [hvals] at h'; exact TyOk.mono hmono (hd.vals y t' h')
          · rw [hrecs, lookup_cons] at h'
            by_cases e : r = r'
            · simp only [e, if_true] at h'; cases h'
              obtain ⟨tn, htn⟩ := hresolved (l, t') (lookup_mem ht')
              exact TyOk.mono hmono (resolve_tyOk hd htn)
            · simp only [e, if_false] at h'; exact TyOk.mono hmono (hd.fields r' tfs' h' l t' ht')
        | val x tn e =>
          obtain ⟨hvalid, hfreshv, hrecs, htypes, τ, je, hres, hc, hvals, rfl⟩ := checkDecl_val hdec
          have hτ : TyOk ctx.recs τ := resolve_tyOk hd hres
          obtain ⟨v, hv, hvt⟩ := checkExpr_sound hc ha hd hτ
          have hnot : (lookup env x).isSome = false := by rw [← ha.1 x, hfreshv]; rfl
          have ha₁ : Agrees ctx₁ ((x, v) :: env) := by
            have := agrees_cons (x := x) ha hvt
            unfold Agrees at this ⊢
            rw [hvals, hrecs]; exact this
          have hd₁ : DeclsOk ctx₁ := by
            refine ⟨fun r' hs => ?_, fun r' tfs' h' => ?_, fun a t' h' => ?_, fun y t' h' => ?_,
              fun r' tfs' h' => ?_⟩
            · rw [hrecs] at hs; rw [htypes]; exact hd.recsTyped r' hs
            · rw [hrecs] at h'; exact hd.labels r' tfs' h'
            · rw [hrecs]; rw [htypes] at h'; exact hd.types a t' h'
            · rw [hrecs]; rw [hvals, lookup_cons] at h'
              by_cases e' : x = y
              · simp only [e', if_true] at h'; cases h'; exact hτ
              · simp only [e', if_false] at h'; exact hd.vals y t' h'
            · rw [hrecs] at h' ⊢; exact hd.fields r' tfs' h'
          obtain ⟨env', hrun, ha', hd'⟩ := ih hrest ha₁ hd₁
          refine ⟨env', ?_, ha', hd'⟩
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
      ⟨fun _ h => by simp [Ctx.empty, lookup] at h, fun _ _ h => by simp [Ctx.empty, lookup] at h,
       fun _ _ h => by simp [Ctx.empty, lookup] at h, fun _ _ h => by simp [Ctx.empty, lookup] at h,
       fun _ _ h => by simp [Ctx.empty, lookup] at h⟩
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
          obtain ⟨_, _, _, _, τ, _, _, _, hvals, _⟩ := checkDecl_val hd
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
          · obtain ⟨_, _, _, _, τ, _, _, _, hvals, _⟩ := checkDecl_val hd
            exact checkFrom_keeps ds hrest x (by rw [hvals]; simp [lookup_cons])
          · exact ih hrest x hx

/-- `compile_sound` is the statement `Counterexamples.lean` refutes for a compiler missing a
    load-bearing check. -/
theorem compile_sound_conclusion : ∀ {p : Program} {out : JS.Program}, compile p = .ok out → Conclusion p out :=
  fun h => compile_sound h

#print axioms compile_sound
#print axioms checkFrom_declares

end LScript
