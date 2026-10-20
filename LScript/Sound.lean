import LScript.Check
import LScript.Typing
import LScript.Counterexamples

/-!
# Soundness

`compile_sound`: if the compiler accepts a program, the module it emits runs without an error in the
model of V8, at some fuel; every name the program declares holds a value of its declared type; and
every name the module exports holds data, never a function. An `Int` is a double that is exactly a
safe integer, a `String` is a string, a record is a frozen object whose own fields are exactly the
record's declared fields, each holding a value of its declared type, and a function is a closure that,
given any value of its parameter type, finishes with a value of its result type. So no field read the
checker accepts gives `undefined`, and no call it accepts throws or runs forever.

`ValOf` at a function type is a logical relation, the standard way to prove that calls finish: it
already says the body finishes for every argument of the parameter type, so a call needs no argument
about termination, and the proof for a lambda is the proof for its body, for each such argument.
-/

namespace LScript

/-! ## The invariant -/

/-- The checker's names are the module's names, and each holds a value of its type. -/
def Agrees (ctx : Ctx) (env : List (String × JS.Val)) : Prop :=
  (∀ x, (lookup ctx.vals x).isSome = (lookup env x).isSome) ∧
  ∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ

/-- A type in scope refers only to declared records. -/
def TyOk (recs : Recs) : Ty → Prop
  | .int => True
  | .str => True
  | .record r => (lookup recs r).isSome
  | .fn a b => TyOk recs a ∧ TyOk recs b

theorem TyOk.mono {recs recs' : Recs} (hr : ∀ r tfs, lookup recs r = some tfs → lookup recs' r = some tfs) :
    ∀ {t}, TyOk recs t → TyOk recs' t
  | .int, _ => trivial
  | .str, _ => trivial
  | .record r, h => by
    simp only [TyOk] at h ⊢
    cases hl : lookup recs r with
    | none => rw [hl] at h; cases h
    | some tfs => rw [hr r tfs hl]; rfl
  | .fn a b, h => by
    simp only [TyOk] at h ⊢
    exact ⟨TyOk.mono hr h.1, TyOk.mono hr h.2⟩

/-- What the declarations so far established, proved once where each is declared: every record is a
    declared type name, so a fresh type name is a fresh record; every record's labels are ones the
    emitted object can carry; every type in scope refers only to declared records; every record's
    fields are data; and every value's name is an identifier. -/
structure DeclsOk (ctx : Ctx) : Prop where
  recsTyped : ∀ r, (lookup ctx.recs r).isSome → (lookup ctx.types r).isSome
  labels : ∀ r tfs, lookup ctx.recs r = some tfs → labelsOk (tfs.map Prod.fst) = true
  types : ∀ a t, lookup ctx.types a = some t → TyOk ctx.recs t
  vals : ∀ x t, lookup ctx.vals x = some t → TyOk ctx.recs t
  fields : ∀ r tfs, lookup ctx.recs r = some tfs → ∀ l t, lookup tfs l = some t → TyOk ctx.recs t
  data : ∀ r tfs, lookup ctx.recs r = some tfs → ∀ l t, lookup tfs l = some t → isData t = true
  idents : ∀ x t, lookup ctx.vals x = some t → JS.validIdent x = true

/-- A function's body is checked with its parameter in scope. -/
theorem DeclsOk.param {ctx x a} (hd : DeclsOk ctx) (hx : JS.validIdent x = true) (ha : TyOk ctx.recs a) :
    DeclsOk { ctx with vals := (x, a) :: ctx.vals } where
  recsTyped := hd.recsTyped
  labels := hd.labels
  types := hd.types
  vals y t h := by
    simp only [lookup_cons] at h
    by_cases e : x = y
    · simp only [e, if_true] at h; cases h; exact ha
    · simp only [e, if_false] at h; exact hd.vals y t h
  fields := hd.fields
  data := hd.data
  idents y t h := by
    simp only [lookup_cons] at h
    by_cases e : x = y
    · subst e; exact hx
    · simp only [e, if_false] at h; exact hd.idents y t h

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

/-- A record type in scope has its fields: the record it names was declared. -/
theorem record_declared {recs : Recs} {r} (h : TyOk recs (.record r)) : ∃ tfs, lookup recs r = some tfs := by
  simp only [TyOk] at h
  cases hl : lookup recs r with
  | none => rw [hl] at h; cases h
  | some tfs => exact ⟨tfs, rfl⟩

/-! ## Declaring a record leaves the meaning of every type in scope unchanged

A function type's parameter is read the other way round from its result, so this is proved in both
directions at once. -/

theorem DataOf.ext_bwd {recs recs' : Recs} (hr : ∀ r tfs, lookup recs r = some tfs → lookup recs' r = some tfs)
    (hc : ∀ r tfs, lookup recs r = some tfs → ∀ l t, lookup tfs l = some t → TyOk recs t)
    {v t} (h : DataOf recs' v t) : TyOk recs t → DataOf recs v t := by
  induction h with
  | int hs => intro _; exact .int hs
  | str => intro _; exact .str
  | obj hl hk hp ih =>
    rename_i fs r tfs'
    intro hok
    obtain ⟨tfs, hl₀⟩ := record_declared hok
    have h₁ := hr r tfs hl₀
    rw [hl] at h₁; cases h₁
    exact .obj hl₀ hk (fun l v τ h1 h2 => ih l v τ h1 h2 (hc r _ hl₀ l τ h2))

theorem ValOf_ext {recs recs' : Recs} (hr : ∀ r tfs, lookup recs r = some tfs → lookup recs' r = some tfs)
    (hc : ∀ r tfs, lookup recs r = some tfs → ∀ l t, lookup tfs l = some t → TyOk recs t) :
    ∀ t, TyOk recs t → ∀ v, (ValOf recs v t ↔ ValOf recs' v t) := by
  intro t
  induction t with
  | int => intro hok v; exact ⟨fun h => DataOf.mono hr h, fun h => DataOf.ext_bwd hr hc h hok⟩
  | str => intro hok v; exact ⟨fun h => DataOf.mono hr h, fun h => DataOf.ext_bwd hr hc h hok⟩
  | record r => intro hok v; exact ⟨fun h => DataOf.mono hr h, fun h => DataOf.ext_bwd hr hc h hok⟩
  | fn a b iha ihb =>
    intro hok v
    simp only [TyOk] at hok
    simp only [ValOf]
    constructor
    · rintro ⟨cenv, x, body, rfl, hf⟩
      refine ⟨cenv, x, body, rfl, fun w hw => ?_⟩
      obtain ⟨n, r, hrun, hrt⟩ := hf w ((iha hok.1 w).mpr hw)
      exact ⟨n, r, hrun, (ihb hok.2 r).mp hrt⟩
    · rintro ⟨cenv, x, body, rfl, hf⟩
      refine ⟨cenv, x, body, rfl, fun w hw => ?_⟩
      obtain ⟨n, r, hrun, hrt⟩ := hf w ((iha hok.1 w).mp hw)
      exact ⟨n, r, hrun, (ihb hok.2 r).mpr hrt⟩

/-- Data of a type is data an importer can be handed. -/
theorem DataOf.data {recs v t} (h : DataOf recs v t) : JS.Data v := by
  induction h with
  | int _ => exact .num
  | str => exact .str
  | obj hl hk hp ih =>
    rename_i fs r tfs
    refine .obj fun l v hv => ?_
    have hs : (lookup tfs l).isSome = true := by rw [← hk l, hv]; rfl
    cases ht : lookup tfs l with
    | none => rw [ht] at hs; cases hs
    | some τ => exact ih l v τ hv ht

/-! ## Labels -/

theorem labelsOk_spec {ls : List String} (h : labelsOk ls = true) :
    ls.all JS.validLabel = true ∧ ls.Nodup := by
  simp only [labelsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem lookup_key {α : Type} {xs : List (String × α)} {l v} (h : lookup xs l = some v) : l ∈ xs.map Prod.fst :=
  List.mem_map.mpr ⟨(l, v), lookup_mem h, rfl⟩

theorem label_shape {l} (h : JS.validLabel l = true) : JS.identShape l = true := by
  simp only [JS.validLabel, Bool.and_eq_true] at h; exact h.1

/-- A field a type declares has a label the emitted code can write. -/
theorem fieldsOfTy_label {ctx : Ctx} (hd : DeclsOk ctx) {t l τ} (h : lookup (fieldsOfTy ctx t) l = some τ) :
    JS.validLabel l = true := by
  cases t with
  | record r =>
    simp only [fieldsOfTy, fieldsOf] at h
    cases hr : lookup ctx.recs r with
    | none => rw [hr] at h; simp [lookup] at h
    | some tfs =>
      rw [hr, Option.getD_some] at h
      exact List.all_eq_true.mp (labelsOk_spec (hd.labels r tfs hr)).1 l (lookup_key h)
  | int => simp [fieldsOfTy, lookup] at h
  | str => simp [fieldsOfTy, lookup] at h
  | fn _ _ => simp [fieldsOfTy, lookup] at h

theorem fieldsOfTy_label_mem {ctx : Ctx} (hd : DeclsOk ctx) {t l τ} (h : (l, τ) ∈ fieldsOfTy ctx t) :
    JS.validLabel l = true := by
  have hs := lookup_isSome_of_mem h
  cases hl : lookup (fieldsOfTy ctx t) l with
  | none => rw [hl] at hs; cases hs
  | some _ => exact fieldsOfTy_label hd hl

theorem fieldPath_shape {ctx : Ctx} (hd : DeclsOk ctx) : ∀ (ls : List String) {t t'},
    fieldPath ctx t ls = .ok t' → ls.all JS.identShape = true := by
  intro ls
  induction ls with
  | nil => intro _ _ _; rfl
  | cons l ls ih =>
    intro t t' h
    simp only [fieldPath] at h
    cases hl : lookup (fieldsOfTy ctx t) l with
    | none => simp [hl] at h
    | some t₁ =>
      simp only [hl] at h
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨label_shape (fieldsOfTy_label hd hl), ih h⟩

/-! ## What the checker emits is valid syntax

V8 parses a function's body before running anything, so the model needs every body valid. -/

theorem inferAtom_static {ctx a t} (hd : DeclsOk ctx) (h : inferAtom ctx a = .ok t) :
    JS.atomOk (emitAtom a) = true := by
  cases a with
  | int n => rfl
  | str s =>
    simp only [inferAtom] at h
    split at h
    · cases h
    · rename_i hs'; simpa [emitAtom, JS.atomOk] using hs'
  | var x =>
    simp only [inferAtom] at h
    cases hx : lookup ctx.vals x with
    | none => simp [hx] at h
    | some τ => simp [emitAtom, JS.atomOk, hd.idents x τ hx]

theorem inferArgs_static {ctx} (hd : DeclsOk ctx) : ∀ (as : List Atom) {ts}, inferArgs ctx as = .ok ts →
    (as.map emitAtom).all JS.atomOk = true := by
  intro as
  induction as with
  | nil => intro _ _; rfl
  | cons a rest ih =>
    intro ts h
    simp only [inferArgs] at h
    cases h₁ : inferAtom ctx a with
    | error _ => simp [h₁] at h
    | ok t =>
      cases h₂ : inferArgs ctx rest with
      | error _ => simp [h₁, h₂] at h
      | ok ts' =>
        simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
        exact ⟨inferAtom_static hd h₁, ih h₂⟩

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

theorem checkExpr_static : ∀ (e : Expr) {ctx τ je}, checkExpr ctx e τ = .ok je → DeclsOk ctx →
    TyOk ctx.recs τ → JS.staticOk je = true := by
  intro e
  induction e with
  | atom a =>
    intro ctx τ je h hd _
    simp only [checkExpr] at h
    cases hi : inferAtom ctx a with
    | error _ => simp [hi] at h
    | ok t =>
      simp only [hi] at h
      split at h
      · cases h
      · cases h; exact inferAtom_static hd hi
  | path x ls =>
    intro ctx τ je h hd _
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
        · cases h
          simp only [JS.staticOk, JS.atomOk, hd.idents x t hx, fieldPath_shape hd ls hp, Bool.and_self]
  | record fs =>
    intro ctx τ je h hd _
    simp only [checkExpr] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hc : checkFields ctx τ fs with
        | error _ => simp [hc] at h
        | ok u =>
          cases u
          simp only [hc] at h
          split at h
          · cases h
          · cases h
            have hspec := checkFields_spec fs hc
            simp only [JS.staticOk, Bool.and_eq_true, List.all_eq_true]
            constructor
            · intro l hl
              obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
              obtain ⟨⟨l', a⟩, hm, rfl⟩ := List.mem_map.mp hp
              obtain ⟨τ', hτ', _⟩ := hspec l' a hm
              exact fieldsOfTy_label hd hτ'
            · intro p hp
              obtain ⟨⟨l', a⟩, hm, rfl⟩ := List.mem_map.mp hp
              obtain ⟨τ', _, hi⟩ := hspec l' a hm
              exact inferAtom_static hd hi
  | update x fs =>
    intro ctx τ je h hd _
    simp only [checkExpr] at h
    cases hx : lookup ctx.vals x with
    | none => simp [hx] at h
    | some t =>
      simp only [hx] at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · cases hc : checkFields ctx t fs with
            | error _ => simp [hc] at h
            | ok u =>
              cases u
              simp only [hc] at h; cases h
              have hspec := checkFields_spec fs hc
              simp only [JS.staticOk, Bool.and_eq_true, List.all_eq_true]
              constructor
              · intro l hl
                obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
                obtain ⟨⟨l', τl⟩, hm, rfl⟩ := List.mem_map.mp hp
                exact fieldsOfTy_label_mem hd hm
              · intro p hp
                obtain ⟨⟨l', τl⟩, hm, rfl⟩ := List.mem_map.mp hp
                dsimp only
                split
                · rename_i a hfl
                  obtain ⟨τ', _, hi⟩ := hspec l' a (lookup_mem hfl)
                  exact inferAtom_static hd hi
                · simp [JS.atomOk, hd.idents x t hx, label_shape (fieldsOfTy_label_mem hd hm)]
  | lam x body ih =>
    intro ctx τ je h hd hτ
    simp only [checkExpr] at h
    split at h
    · cases h
    · rename_i hfn'
      split at h
      · cases h
      · rename_i hb'
        have hb : JS.bindable x = true := by simpa using hb'
        have hident : JS.validIdent x = true := by simp only [JS.bindable, Bool.and_eq_true] at hb; exact hb.1
        cases hc : checkExpr { ctx with vals := (x, paramTy τ) :: ctx.vals } body (resultTy τ) with
        | error _ => simp [hc] at h
        | ok jb =>
          simp only [hc, Except.ok.injEq] at h; subst h
          cases τ with
          | fn a b =>
            simp only [TyOk] at hτ
            simp only [JS.staticOk, hident, Bool.true_and]
            exact ih hc (hd.param hident hτ.1) hτ.2
          | int => simp [isFn] at hfn'
          | str => simp [isFn] at hfn'
          | record _ => simp [isFn] at hfn'
  | app f a more =>
    intro ctx τ je h hd _
    simp only [checkExpr] at h
    cases hf : lookup ctx.vals f with
    | none => simp [hf] at h
    | some t =>
      simp only [hf] at h
      cases hargs : inferArgs ctx (a :: more) with
      | error _ => simp [hargs] at h
      | ok ts =>
        simp only [hargs] at h
        split at h
        · cases h
        · cases h
          have hs := inferArgs_static hd (a :: more) hargs
          simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hs
          have hfok : JS.atomOk (.path f []) = true := by simp [JS.atomOk, hd.idents f t hf]
          simp only [JS.staticOk, hfok, hs.1, hs.2, Bool.and_self]

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
      exact ⟨.num n, by simp [emitAtom, JS.evalAtom, hs], (DataOf.int hs).valOf⟩
  | str s =>
    simp only [inferAtom] at h
    split at h
    · cases h
    · rename_i hs'
      cases h
      have hs : JS.validStr s = true := by simpa using hs'
      exact ⟨.str s, by simp [emitAtom, JS.evalAtom, hs], DataOf.str.valOf⟩
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
    fieldPath ctx t ls = .ok t' → ValOf ctx.recs v t → ∃ w, JS.readPath v ls = .ok w ∧ ValOf ctx.recs w t' := by
  intro ls
  induction ls with
  | nil => intro t t' v h hv; simp only [fieldPath] at h; cases h; exact ⟨v, rfl, hv⟩
  | cons l ls ih =>
    intro t t' v h hv
    simp only [fieldPath] at h
    cases t with
    | int => simp [fieldsOfTy, lookup] at h
    | str => simp [fieldsOfTy, lookup] at h
    | fn _ _ => simp [fieldsOfTy, lookup] at h
    | record r =>
      have hv' : DataOf ctx.recs v (.record r) := hv
      cases hv' with
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
            have hw := (hp l w t₁ hfl hl).valOf
            have : JS.readPath (.obj fs true) (l :: ls) = JS.readPath w ls := by
              simp [JS.readPath, JS.readField, hfl]
            rw [this]; exact ih h hw

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

theorem evalExpr_obj {n} {env : List (String × JS.Val)} {fs : List (String × JS.Atom)} {vs}
    (hv : (fs.map Prod.fst).all JS.validLabel = true) (hn : (fs.map Prod.fst).Nodup)
    (he : JS.evalFields env fs = .ok vs) : JS.evalExpr (n + 1) env (.obj fs) = .ok (.obj vs true) := by
  simp [JS.evalExpr, hv, hn, he]

/-- Applying a function value to arguments the checker typed, one at a time, gives a value of the type
    left after them, given enough fuel for every body. -/
theorem apply_sound {ctx env} (ha : Agrees ctx env) : ∀ (as : List Atom) {ts fv τ}, inferArgs ctx as = .ok ts →
    ValOf ctx.recs fv (arrowTy ts τ) →
    ∃ ws N r, JS.evalArgs env (as.map emitAtom) = .ok ws ∧
      JS.applyAll (fun env' e' => JS.evalExpr N env' e') (.ok fv) ws = .ok r ∧ ValOf ctx.recs r τ := by
  intro as
  induction as with
  | nil =>
    intro ts fv τ h hf
    simp only [inferArgs, Except.ok.injEq] at h; subst h
    exact ⟨[], 0, fv, rfl, by simp [JS.applyAll], hf⟩
  | cons a rest ih =>
    intro ts fv τ h hf
    simp only [inferArgs] at h
    cases h₁ : inferAtom ctx a with
    | error _ => simp [h₁] at h
    | ok t₀ =>
      cases h₂ : inferArgs ctx rest with
      | error _ => simp [h₁, h₂] at h
      | ok ts' =>
        simp only [h₁, h₂, Except.ok.injEq] at h; subst h
        simp only [arrowTy, ValOf] at hf
        obtain ⟨cenv, x, body, rfl, hbody⟩ := hf
        obtain ⟨w₀, hw₀, hw₀t⟩ := inferAtom_sound h₁ ha
        obtain ⟨n₁, r₁, hr₁, hr₁t⟩ := hbody w₀ hw₀t
        obtain ⟨ws, N₂, r, hws, happ, hrt⟩ := ih h₂ hr₁t
        refine ⟨w₀ :: ws, max n₁ N₂, r, by simp [JS.evalArgs, hw₀, hws], ?_, hrt⟩
        simp only [JS.applyAll]
        rw [JS.evalExpr_mono n₁ hr₁ (by simp) _ (Nat.le_max_left _ _)]
        exact JS.applyAll_mono (fun _ _ _ h₁ h₂ => JS.evalExpr_mono N₂ h₁ h₂ _ (Nat.le_max_right _ _)) ws happ (by simp)

/-- What the checker accepts against a type in scope, the emitted JavaScript evaluates to a value
    of it, given enough fuel. -/
theorem checkExpr_sound : ∀ (e : Expr) {ctx env τ je}, checkExpr ctx e τ = .ok je → Agrees ctx env →
    DeclsOk ctx → TyOk ctx.recs τ → ∃ n v, JS.evalExpr n env je = .ok v ∧ ValOf ctx.recs v τ := by
  intro e
  induction e with
  | atom a =>
    intro ctx env τ je h ha hd hτ
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
        exact ⟨1, v, by simpa [JS.evalExpr] using hv, hvt⟩
  | path x ls =>
    intro ctx env τ je h ha hd hτ
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
          obtain ⟨w, hw, hwt⟩ := fieldPath_sound ls hp hvt
          have hls := fieldPath_shape hd ls hp
          exact ⟨1, w, by simp [JS.evalExpr, JS.evalAtom, hls, hv, hw], hwt⟩
  | record fs =>
    intro ctx env τ je h ha hd hτ
    simp only [checkExpr] at h
    split at h
    · cases h
    · rename_i hrec'
      have hrec : isRecord τ = true := by simpa using hrec'
      cases τ with
      | int => simp [isRecord] at hrec
      | str => simp [isRecord] at hrec
      | fn _ _ => simp [isRecord] at hrec
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
            refine ⟨1, .obj vs true, ?_, (DataOf.obj hr (fun l => ?_) (fun l v τ' hv hτ' => ?_)).valOf⟩
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
              rw [hτ'] at h₁; cases h₁
              exact h₂.dataOf (hd.data r tfs hr l _ hτ')
  | update x fs =>
    intro ctx env τ je h ha hd hτ
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
        | fn _ _ => simp [isRecord] at hrec
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
              have hvxt' : DataOf ctx.recs vx (.record r) := hvxt
              cases hvxt' with
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
                        refine ⟨w, ?_, τl, hτl, (hp l' w τl hxl hτl).valOf⟩
                        have hshape := label_shape (List.all_eq_true.mp htvalid l' (lookup_key hτl))
                        simp [JS.evalAtom, hshape, hvx, JS.readPath, JS.readField, hxl])
                refine ⟨1, .obj vs true, ?_, (DataOf.obj hr (fun l => ?_) (fun l v τ' hv hτ' => ?_)).valOf⟩
                · have hv' : (efs.map Prod.fst).all JS.validLabel = true := by rw [hkeys₁]; exact htvalid
                  have hn' : (efs.map Prod.fst).Nodup := by rw [hkeys₁]; exact htnodup
                  exact evalExpr_obj hv' hn' hvs
                · exact lookup_isSome_keys (hkeys.trans hkeys₁)
                · obtain ⟨τ'', h₁, h₂⟩ := hq l v hv
                  rw [hτ'] at h₁; cases h₁
                  exact h₂.dataOf (hd.data r tfs hr l _ hτ')
  | lam x body ih =>
    intro ctx env τ je h ha hd hτ
    have hstatic := checkExpr_static (.lam x body) h hd hτ
    simp only [checkExpr] at h
    split at h
    · cases h
    · rename_i hfn'
      split at h
      · cases h
      · rename_i hb'
        have hb : JS.bindable x = true := by simpa using hb'
        have hident : JS.validIdent x = true := by simp only [JS.bindable, Bool.and_eq_true] at hb; exact hb.1
        have hglobal : JS.emittedGlobals.contains x = false := by
          simp only [JS.bindable, Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.2
        cases hc : checkExpr { ctx with vals := (x, paramTy τ) :: ctx.vals } body (resultTy τ) with
        | error _ => simp [hc] at h
        | ok jb =>
          simp only [hc, Except.ok.injEq] at h; subst h
          cases τ with
          | fn a b =>
            simp only [TyOk] at hτ
            simp only [JS.staticOk, hident, Bool.true_and] at hstatic
            refine ⟨1, .clos env x jb, ?_, ?_⟩
            · simp only [JS.evalExpr, hident, hglobal, hstatic, Bool.not_true, Bool.false_eq_true, if_false]
            · simp only [ValOf]
              refine ⟨env, x, jb, rfl, fun w hw => ?_⟩
              obtain ⟨n, r, h₁, h₂⟩ := ih hc (agrees_cons ha hw) (hd.param hident hτ.1) hτ.2
              exact ⟨n, r, h₁, h₂⟩
          | int => simp [isFn] at hfn'
          | str => simp [isFn] at hfn'
          | record _ => simp [isFn] at hfn'
  | app f a more =>
    intro ctx env τ je h ha hd hτ
    simp only [checkExpr] at h
    cases hf : lookup ctx.vals f with
    | none => simp [hf] at h
    | some t =>
      simp only [hf] at h
      cases hargs : inferArgs ctx (a :: more) with
      | error _ => simp [hargs] at h
      | ok ts =>
        simp only [hargs] at h
        split at h
        · cases h
        · rename_i ht'
          have ht : t = arrowTy ts τ := by simpa using ht'
          cases h
          obtain ⟨fv, hfv, hfvt⟩ := ha.2 f t hf
          rw [ht] at hfvt
          obtain ⟨ws, N, r, hws, happ, hr⟩ := apply_sound ha (a :: more) hargs hfvt
          refine ⟨N + 1, r, ?_, hr⟩
          have hfa : JS.evalAtom env (.path f []) = .ok fv := by simp [JS.evalAtom, hfv, JS.readPath]
          simp only [List.map_cons] at hws
          simp only [JS.evalExpr, hfa, hws]
          exact happ

/-! ## Declarations -/

theorem resolve_tyOk {ctx} (hd : DeclsOk ctx) : ∀ {tn t}, resolve ctx.types tn = .ok t → TyOk ctx.recs t
  | .int, _, h => by simp only [resolve] at h; cases h; trivial
  | .str, _, h => by simp only [resolve] at h; cases h; trivial
  | .named a, _, h => by
    simp only [resolve] at h
    cases hl : lookup ctx.types a with
    | none => simp [hl] at h
    | some t' => simp only [hl] at h; cases h; exact hd.types a _ hl
  | .fn a b, _, h => by
    simp only [resolve] at h
    cases ha : resolve ctx.types a with
    | error _ => simp [ha] at h
    | ok ta =>
      cases hb : resolve ctx.types b with
      | error _ => simp [ha, hb] at h
      | ok tb =>
        simp only [ha, hb, Except.ok.injEq] at h; subst h
        simp only [TyOk]
        exact ⟨resolve_tyOk hd ha, resolve_tyOk hd hb⟩

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
      ∃ tfs, resolveFields ctx.types fields = .ok tfs ∧ tfs.all (fun p => isData p.2) = true ∧
        ctx'.recs = (r, tfs) :: ctx.recs ∧ ctx'.types = (r, .record r) :: ctx.types := by
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
          simp only [hr] at h
          split at h
          · cases h
          · rename_i hdata
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hdata' : tfs.all (fun p => isData p.2) = true := by
              cases hb : tfs.all (fun p => isData p.2) with
              | true => rfl
              | false => rw [hb] at hdata; simp at hdata
            refine ⟨rfl, rfl, ?_, by simpa using hlab, tfs, rfl, hdata', rfl, rfl⟩
            cases hl : lookup ctx.types r with
            | none => rfl
            | some _ => simp [hl] at hfresh

theorem checkDecl_val {ctx x tn e ctx' jd} (h : checkDecl ctx (.val x tn e) = .ok (ctx', jd)) :
    JS.bindable x = true ∧ lookup ctx.vals x = none ∧ ctx'.recs = ctx.recs ∧ ctx'.types = ctx.types ∧
      ∃ τ je, resolve ctx.types tn = .ok τ ∧ checkExpr ctx e τ = .ok je ∧
        ctx'.vals = (x, τ) :: ctx.vals ∧ jd = some ⟨x, je, isData τ⟩ := by
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

/-- The invariant carries through the program, declaration by declaration, and every name the module
    exports holds data. -/
theorem checkFrom_sound : ∀ (p : Program) {ctx ctx' js env}, checkFrom ctx p = .ok (ctx', js) →
    Agrees ctx env → DeclsOk ctx →
    ∃ n env', JS.runFrom n env js = .ok env' ∧ Agrees ctx' env' ∧ DeclsOk ctx' ∧
      ∀ d ∈ js, d.exported = true → ∃ v, lookup env' d.name = some v ∧ JS.Data v := by
  intro p
  induction p with
  | nil =>
    intro ctx ctx' js env h ha hd
    simp only [checkFrom, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, env, rfl, ha, hd, fun d hd => by simp at hd⟩
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
            fun r' tfs' h' => ?_, fun r' tfs' h' => ?_, fun y t' h' => ?_⟩
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
          · rw [hrecs] at h'; exact hd.data r' tfs' h'
          · rw [hvals] at h'; exact hd.idents y t' h'
        | record r fields =>
          obtain ⟨rfl, hvals, hfresh, hlab, tfs, hres, hdata, hrecs, htypes⟩ := checkDecl_record hdec
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
            exact ⟨v, hv, (ValOf_ext hmono hd.fields τ (hd.vals y τ hy) v).mp hvt⟩
          obtain ⟨hkeys, hresolved⟩ := resolveFields_spec fields hres
          refine ih hrest ha₁ ⟨fun r' hs => ?_, fun r' tfs' h' => ?_, fun a t' h' => ?_, fun y t' h' => ?_,
            fun r' tfs' h' l t' ht' => ?_, fun r' tfs' h' l t' ht' => ?_, fun y t' h' => ?_⟩
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
          · rw [hrecs, lookup_cons] at h'
            by_cases e : r = r'
            · simp only [e, if_true] at h'; cases h'
              exact List.all_eq_true.mp hdata (l, t') (lookup_mem ht')
            · simp only [e, if_false] at h'; exact hd.data r' tfs' h' l t' ht'
          · rw [hvals] at h'; exact hd.idents y t' h'
        | val x tn e =>
          obtain ⟨hvalid, hfreshv, hrecs, htypes, τ, je, hres, hc, hvals, rfl⟩ := checkDecl_val hdec
          have hτ : TyOk ctx.recs τ := resolve_tyOk hd hres
          obtain ⟨n₁, v, hv, hvt⟩ := checkExpr_sound e hc ha hd hτ
          have hnot : (lookup env x).isSome = false := by rw [← ha.1 x, hfreshv]; rfl
          have hident : JS.validIdent x = true := by simp only [JS.bindable, Bool.and_eq_true] at hvalid; exact hvalid.1
          have hglobal : JS.emittedGlobals.contains x = false := by
            simp only [JS.bindable, Bool.and_eq_true, Bool.not_eq_true'] at hvalid; exact hvalid.2
          have ha₁ : Agrees ctx₁ ((x, v) :: env) := by
            have := agrees_cons (x := x) ha hvt
            unfold Agrees at this ⊢
            rw [hvals, hrecs]; exact this
          have hd₁ : DeclsOk ctx₁ := by
            refine ⟨fun r' hs => ?_, fun r' tfs' h' => ?_, fun a t' h' => ?_, fun y t' h' => ?_,
              fun r' tfs' h' => ?_, fun r' tfs' h' => ?_, fun y t' h' => ?_⟩
            · rw [hrecs] at hs; rw [htypes]; exact hd.recsTyped r' hs
            · rw [hrecs] at h'; exact hd.labels r' tfs' h'
            · rw [hrecs]; rw [htypes] at h'; exact hd.types a t' h'
            · rw [hrecs]; rw [hvals, lookup_cons] at h'
              by_cases e' : x = y
              · simp only [e', if_true] at h'; cases h'; exact hτ
              · simp only [e', if_false] at h'; exact hd.vals y t' h'
            · rw [hrecs] at h' ⊢; exact hd.fields r' tfs' h'
            · rw [hrecs] at h'; exact hd.data r' tfs' h'
            · rw [hvals, lookup_cons] at h'
              by_cases e' : x = y
              · subst e'; exact hident
              · simp only [e', if_false] at h'; exact hd.idents y t' h'
          obtain ⟨n₂, env', hrun, ha', hd', hexp⟩ := ih hrest ha₁ hd₁
          refine ⟨max n₁ n₂, env', ?_, ha', hd', fun d hdm hdx => ?_⟩
          · simp only [JS.runFrom, hident, hglobal, Bool.not_true, Bool.false_eq_true, if_false, hnot]
            rw [JS.evalExpr_mono n₁ hv (by simp) _ (Nat.le_max_left _ _)]
            exact JS.runFrom_mono _ hrun (by simp) _ (Nat.le_max_right _ _)
          · simp only [List.mem_cons] at hdm
            rcases hdm with rfl | hdm
            · exact ⟨v, JS.runFrom_keeps js' hrun (by simp [lookup_cons]), (hvt.dataOf hdx).data⟩
            · exact hexp d hdm hdx

/-- **Soundness.** If the compiler accepts a program, the module it emits runs without an error, given
    enough fuel; every name the checker declared holds a value of its declared type; and every name the
    module exports holds data, never a function. -/
theorem compile_sound {p : Program} {out : JS.Program} (h : compile p = .ok out) :
    ∃ ctx env, check p = .ok (ctx, out) ∧ (∃ n, JS.run n out = .ok env) ∧
      (∀ x τ, lookup ctx.vals x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ) ∧
      ∀ d ∈ out, d.exported = true → ∃ v, lookup env d.name = some v ∧ JS.Data v := by
  simp only [compile] at h
  cases hc : check p with
  | error _ => simp [hc] at h
  | ok res =>
    obtain ⟨ctx, js⟩ := res
    simp only [hc, Except.ok.injEq] at h; subst h
    obtain ⟨n, env, hrun, ha, _, hexp⟩ := checkFrom_sound p (env := []) hc
      ⟨fun _ => rfl, fun _ _ h => by simp [Ctx.empty, lookup] at h⟩
      ⟨fun _ h => by simp [Ctx.empty, lookup] at h, fun _ _ h => by simp [Ctx.empty, lookup] at h,
       fun _ _ h => by simp [Ctx.empty, lookup] at h, fun _ _ h => by simp [Ctx.empty, lookup] at h,
       fun _ _ h => by simp [Ctx.empty, lookup] at h, fun _ _ h => by simp [Ctx.empty, lookup] at h,
       fun _ _ h => by simp [Ctx.empty, lookup] at h⟩
    exact ⟨ctx, env, rfl, ⟨n, hrun⟩, ha.2, hexp⟩

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
