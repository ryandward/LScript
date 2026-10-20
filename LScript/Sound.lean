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
  (∀ x, (ctx.vals.find x).isSome = (lookup env x).isSome) ∧
  ∀ x τ, ctx.vals.find x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ

/-- A type in scope refers only to declared records. -/
def TyOk (recs : Recs) : Ty → Prop
  | .int => True
  | .str => True
  | .record r => (recs.find r).isSome
  | .fn a b => TyOk recs a ∧ TyOk recs b
  | .entry a b => TyOk recs a ∧ TyOk recs b

theorem TyOk.mono {recs recs' : Recs} (hr : ∀ r tfs, recs.find r = some tfs → recs'.find r = some tfs) :
    ∀ {t}, TyOk recs t → TyOk recs' t
  | .int, _ => trivial
  | .str, _ => trivial
  | .record r, h => by
    simp only [TyOk] at h ⊢
    cases hl : recs.find r with
    | none => rw [hl] at h; cases h
    | some tfs => rw [hr r tfs hl]; rfl
  | .fn a b, h => by
    simp only [TyOk] at h ⊢
    exact ⟨TyOk.mono hr h.1, TyOk.mono hr h.2⟩
  | .entry a b, h => by
    simp only [TyOk] at h ⊢
    exact ⟨TyOk.mono hr h.1, TyOk.mono hr h.2⟩

/-- What the declarations so far established, proved once where each is declared: every record is a
    declared type name, so a fresh type name is a fresh record; every record's labels are ones the
    emitted object can carry; every type in scope refers only to declared records; every record's
    fields are data; and every value's name is an identifier. -/
structure DeclsOk (ctx : Ctx) : Prop where
  recsTyped : ∀ r, (ctx.recs.find r).isSome → (ctx.types.find r).isSome
  labels : ∀ r tfs, ctx.recs.find r = some tfs → labelsOk (tfs.map Prod.fst) = true
  types : ∀ a t, ctx.types.find a = some t → TyOk ctx.recs t
  vals : ∀ x t, ctx.vals.find x = some t → TyOk ctx.recs t
  fields : ∀ r tfs, ctx.recs.find r = some tfs → ∀ l t, lookup tfs l = some t → TyOk ctx.recs t
  data : ∀ r tfs, ctx.recs.find r = some tfs → ∀ l t, lookup tfs l = some t → isData t = true
  idents : ∀ x t, ctx.vals.find x = some t → JS.validIdent x = true

/-- A function's body is checked with its parameter in scope. -/
theorem DeclsOk.param {ctx x a} (hd : DeclsOk ctx) (hx : JS.validIdent x = true) (ha : TyOk ctx.recs a) :
    DeclsOk { ctx with vals := ctx.vals.insert x a } where
  recsTyped := hd.recsTyped
  labels := hd.labels
  types := hd.types
  vals y t h := by
    simp only [Scope.find_insert] at h
    by_cases e : x = y
    · simp only [e, if_true] at h; cases h; exact ha
    · simp only [e, if_false] at h; exact hd.vals y t h
  fields := hd.fields
  data := hd.data
  idents y t h := by
    simp only [Scope.find_insert] at h
    by_cases e : x = y
    · subst e; exact hx
    · simp only [e, if_false] at h; exact hd.idents y t h

/-- A value or an entry declared with a type in scope. -/
theorem DeclsOk.declare {ctx ctx₁ : Ctx} {x τ} (hd : DeclsOk ctx) (hrecs : ctx₁.recs = ctx.recs)
    (htypes : ctx₁.types = ctx.types) (hvals : ctx₁.vals = ctx.vals.insert x τ) (hτ : TyOk ctx.recs τ)
    (hx : JS.validIdent x = true) : DeclsOk ctx₁ := by
  have : ctx₁ = { ctx with vals := ctx.vals.insert x τ } := by
    cases ctx₁; cases ctx; simp only at hrecs htypes hvals; subst hrecs htypes hvals; rfl
  subst this; exact hd.param hx hτ

theorem agrees_cons {ctx env x t v} (h : Agrees ctx env) (hv : ValOf ctx.recs v t) :
    Agrees { ctx with vals := ctx.vals.insert x t } ((x, v) :: env) := by
  refine ⟨fun y => ?_, fun y τ hy => ?_⟩
  · simp only [Scope.find_insert, lookup_cons]
    by_cases e : x = y
    · simp [e]
    · simp only [e, if_false]; exact h.1 y
  · simp only [Scope.find_insert, lookup_cons] at hy ⊢
    by_cases e : x = y
    · simp only [e, if_true] at hy ⊢; cases hy; exact ⟨v, rfl, hv⟩
    · simp only [e, if_false] at hy ⊢; exact h.2 y τ hy

/-- A record type in scope has its fields: the record it names was declared. -/
theorem record_declared {recs : Recs} {r} (h : TyOk recs (.record r)) : ∃ tfs, recs.find r = some tfs := by
  simp only [TyOk] at h
  cases hl : recs.find r with
  | none => rw [hl] at h; cases h
  | some tfs => exact ⟨tfs, rfl⟩

/-! ## Declaring a record leaves the meaning of every type in scope unchanged

A function type's parameter is read the other way round from its result, so this is proved in both
directions at once. -/

theorem DataOf.ext_bwd {recs recs' : Recs} (hr : ∀ r tfs, recs.find r = some tfs → recs'.find r = some tfs)
    (hc : ∀ r tfs, recs.find r = some tfs → ∀ l t, lookup tfs l = some t → TyOk recs t)
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

theorem ValOf_ext {recs recs' : Recs} (hr : ∀ r tfs, recs.find r = some tfs → recs'.find r = some tfs)
    (hc : ∀ r tfs, recs.find r = some tfs → ∀ l t, lookup tfs l = some t → TyOk recs t) :
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
  | entry a b _ ihb =>
    intro hok v
    simp only [TyOk] at hok
    simp only [ValOf]
    constructor
    · rintro ⟨c, rfl, hc⟩
      refine ⟨c, rfl, fun j hj => ?_⟩
      obtain ⟨n, r, hrun, hrt, hrd⟩ := hc j hj
      exact ⟨n, r, hrun, (ihb hok.2 r).mp hrt, hrd⟩
    · rintro ⟨c, rfl, hc⟩
      refine ⟨c, rfl, fun j hj => ?_⟩
      obtain ⟨n, r, hrun, hrt, hrd⟩ := hc j hj
      exact ⟨n, r, hrun, (ihb hok.2 r).mpr hrt, hrd⟩

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

theorem DataOf.not_callable {recs v t} (h : DataOf recs v t) : JS.callable v = false := by
  cases h <;> rfl

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
    cases hr : ctx.recs.find r with
    | none => rw [hr] at h; simp [lookup] at h
    | some tfs =>
      rw [hr, Option.getD_some] at h
      exact List.all_eq_true.mp (labelsOk_spec (hd.labels r tfs hr)).1 l (lookup_key h)
  | int => simp [fieldsOfTy, lookup] at h
  | str => simp [fieldsOfTy, lookup] at h
  | fn _ _ => simp [fieldsOfTy, lookup] at h
  | entry _ _ => simp [fieldsOfTy, lookup] at h

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
    cases hx : ctx.vals.find x with
    | none => simp [hx] at h
    | some τ => simp [emitAtom, JS.atomOk, hd.idents x τ hx]

theorem emitCall_static {ctx} (hd : DeclsOk ctx) : ∀ (as : List Atom) {ts f}, inferArgs ctx as = .ok ts →
    JS.staticOk f = true → JS.staticOk (emitCall f as) = true := by
  intro as
  induction as with
  | nil => intro _ _ _ hf; exact hf
  | cons a rest ih =>
    intro ts f h hf
    simp only [inferArgs] at h
    cases h₁ : inferAtom ctx a with
    | error _ => simp [h₁] at h
    | ok t =>
      cases h₂ : inferArgs ctx rest with
      | error _ => simp [h₁, h₂] at h
      | ok ts' =>
        apply ih h₂
        simp only [JS.staticOk, hf, inferAtom_static hd h₁, Bool.and_self]

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
    cases hx : ctx.vals.find x with
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
    cases hx : ctx.vals.find x with
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
        cases hc : checkExpr { ctx with vals := ctx.vals.insert x (paramTy τ) } body (resultTy τ) with
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
          | entry _ _ => simp [isFn] at hfn'
  | app f a more =>
    intro ctx τ je h hd _
    simp only [checkExpr] at h
    cases hf : ctx.vals.find f with
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
          have hfok : JS.staticOk (.atom (.path f [])) = true := by simp [JS.staticOk, JS.atomOk, hd.idents f t hf]
          exact emitCall_static hd (a :: more) hargs hfok

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
    cases hx : ctx.vals.find x with
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
    | entry _ _ => simp [fieldsOfTy, lookup] at h
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
theorem apply_sound {ctx env} (ha : Agrees ctx env) : ∀ (as : List Atom) {ts f fv τ n₀},
    inferArgs ctx as = .ok ts → JS.evalExpr n₀ env f = .ok fv → ValOf ctx.recs fv (arrowTy ts τ) →
    ∃ N r, JS.evalExpr N env (emitCall f as) = .ok r ∧ ValOf ctx.recs r τ := by
  intro as
  induction as with
  | nil =>
    intro ts f fv τ n₀ h hf hfv
    simp only [inferArgs, Except.ok.injEq] at h; subst h
    exact ⟨n₀, fv, hf, hfv⟩
  | cons a rest ih =>
    intro ts f fv τ n₀ h hf hfv
    simp only [inferArgs] at h
    cases h₁ : inferAtom ctx a with
    | error _ => simp [h₁] at h
    | ok t₀ =>
      cases h₂ : inferArgs ctx rest with
      | error _ => simp [h₁, h₂] at h
      | ok ts' =>
        simp only [h₁, h₂, Except.ok.injEq] at h; subst h
        simp only [arrowTy, ValOf] at hfv
        obtain ⟨cenv, x, body, rfl, hbody⟩ := hfv
        obtain ⟨w₀, hw₀, hw₀t⟩ := inferAtom_sound h₁ ha
        obtain ⟨n₁, r₁, hr₁, hr₁t⟩ := hbody w₀ hw₀t
        -- One unit of fuel more than the function, its argument and the body each need.
        obtain ⟨M, hM⟩ : ∃ M, max (max n₀ n₁) 1 = M + 1 := ⟨max (max n₀ n₁) 1 - 1, by omega⟩
        have hf' := JS.evalExpr_mono n₀ hf (by simp) (M + 1) (by omega)
        have hr₁' := JS.evalExpr_mono n₁ hr₁ (by simp) (M + 1) (by omega)
        have happ : JS.evalExpr (M + 2) env (.app f (.atom (emitAtom a))) = .ok r₁ := by
          simp only [JS.evalExpr, hf', hw₀, hr₁']
        exact ih h₂ happ hr₁t

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
    cases hx : ctx.vals.find x with
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
      | entry _ _ => simp [isRecord] at hrec
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
    cases hx : ctx.vals.find x with
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
        | entry _ _ => simp [isRecord] at hrec
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
        cases hc : checkExpr { ctx with vals := ctx.vals.insert x (paramTy τ) } body (resultTy τ) with
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
          | entry _ _ => simp [isFn] at hfn'
  | app f a more =>
    intro ctx env τ je h ha hd hτ
    simp only [checkExpr] at h
    cases hf : ctx.vals.find f with
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
          have hfa : JS.evalExpr 1 env (.atom (.path f [])) = .ok fv := by
            simp [JS.evalExpr, JS.evalAtom, hfv, JS.readPath]
          exact apply_sound ha (a :: more) hargs hfa hfvt

/-! ## Entries

An entry's parse is evaluated on anything `JSON.parse` returns, or `undefined`. Its test never errors
on one of those, since it reads a field only once the shape test has found it; and once the test
holds, the build is data of the input type, from the declared fields only. -/

theorem evalTest_and_true {env t u} :
    JS.evalTest env (.and t u) = .ok true ↔ JS.evalTest env t = .ok true ∧ JS.evalTest env u = .ok true := by
  simp only [JS.evalTest]
  cases JS.evalTest env t with
  | error e => simp
  | ok b => cases b <;> simp

theorem foldl_and_false {env} {g : String × Ty → JS.Test} : ∀ (xs : List (String × Ty)) {t₀},
    JS.evalTest env t₀ = .ok false → JS.evalTest env (xs.foldl (fun acc p => .and acc (g p)) t₀) = .ok false
  | [], _, h => h
  | _ :: xs, _, h => foldl_and_false xs (by simp [JS.evalTest, h])

theorem foldl_and_total {env} {g : String × Ty → JS.Test} : ∀ (xs : List (String × Ty)) {t₀},
    JS.evalTest env t₀ = .ok true → (∀ p ∈ xs, ∃ b, JS.evalTest env (g p) = .ok b) →
    ∃ b, JS.evalTest env (xs.foldl (fun acc p => .and acc (g p)) t₀) = .ok b
  | [], _, h, _ => ⟨true, h⟩
  | x :: xs, _, h, hg => by
    obtain ⟨b, hb⟩ := hg x List.mem_cons_self
    cases b with
    | true => exact foldl_and_total xs (by simp [JS.evalTest, h, hb]) (fun p hp => hg p (List.mem_cons_of_mem _ hp))
    | false => exact ⟨false, foldl_and_false xs (by simp [JS.evalTest, h, hb])⟩

theorem foldl_and_true {env} {g : String × Ty → JS.Test} : ∀ (xs : List (String × Ty)) {t₀},
    JS.evalTest env (xs.foldl (fun acc p => .and acc (g p)) t₀) = .ok true →
    JS.evalTest env t₀ = .ok true ∧ ∀ p ∈ xs, JS.evalTest env (g p) = .ok true
  | [], _, h => ⟨h, fun _ hp => by simp at hp⟩
  | x :: xs, _, h => by
    obtain ⟨h₁, h₂⟩ := foldl_and_true xs h
    obtain ⟨h₃, h₄⟩ := evalTest_and_true.mp h₁
    refine ⟨h₃, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h₄
    · exact h₂ p hp

theorem foldl_and_testOk {g : String × Ty → JS.Test} : ∀ (xs : List (String × Ty)) {t₀},
    JS.testOk t₀ = true → (∀ p ∈ xs, JS.testOk (g p) = true) →
    JS.testOk (xs.foldl (fun acc p => .and acc (g p)) t₀) = true
  | [], _, h, _ => h
  | x :: xs, _, h, hg =>
    foldl_and_testOk xs (by simp [JS.testOk, h, hg x List.mem_cons_self]) (fun p hp => hg p (List.mem_cons_of_mem _ hp))

theorem evalTest_atom {env a u} {f : JS.Val → Except JS.Err Bool} (ha : JS.evalAtom env a = .ok u) :
    (JS.evalAtom env a >>= f) = f u := by
  rw [ha]; rfl

theorem testField_total {env a u} (t : Ty) (ha : JS.evalAtom env a = .ok u) (hu : u ≠ .untracked) :
    ∃ b, JS.evalTest env (testField t a) = .ok b := by
  have hs : ∃ b, JS.isStrVal u = .ok b := by cases u <;> simp_all [JS.isStrVal]
  have hi : ∃ b, JS.isIntVal u = .ok b := by cases u <;> simp_all [JS.isIntVal]
  obtain ⟨bs, hbs⟩ := hs
  obtain ⟨bi, hbi⟩ := hi
  have hnever : ∃ b, JS.evalTest env (never a) = .ok b := by
    cases bs with
    | true => exact ⟨bi, by simp [never, JS.evalTest, evalTest_atom ha, hbs, hbi]⟩
    | false => exact ⟨false, by simp [never, JS.evalTest, evalTest_atom ha, hbs]⟩
  cases t with
  | int => exact ⟨bi, by simp [testField, JS.evalTest, evalTest_atom ha, hbi]⟩
  | str => exact ⟨bs, by simp [testField, JS.evalTest, evalTest_atom ha, hbs]⟩
  | record _ => exact hnever
  | fn _ _ => exact hnever
  | entry _ _ => exact hnever

theorem never_false {env a} (h : JS.evalTest env (never a) = .ok true) : False := by
  obtain ⟨h₁, h₂⟩ := evalTest_and_true.mp h
  simp only [JS.evalTest] at h₁ h₂
  cases ha : JS.evalAtom env a with
  | error e => rw [ha] at h₁; cases h₁
  | ok u =>
    rw [evalTest_atom ha] at h₁ h₂
    cases u <;> simp [JS.isStrVal, JS.isIntVal] at h₁ h₂

theorem testField_true {recs env a u} (t : Ty) (ha : JS.evalAtom env a = .ok u)
    (h : JS.evalTest env (testField t a) = .ok true) : DataOf recs u t := by
  cases t with
  | int =>
    simp only [testField, JS.evalTest, evalTest_atom ha] at h
    cases u <;> simp [JS.isIntVal] at h
    exact .int h
  | str =>
    simp only [testField, JS.evalTest, evalTest_atom ha] at h
    cases u <;> simp [JS.isStrVal] at h
    exact .str
  | record _ => exact (never_false h).elim
  | fn _ _ => exact (never_false h).elim
  | entry _ _ => exact (never_false h).elim

theorem fieldsOf_label {ctx : Ctx} (hd : DeclsOk ctx) {r p} (hp : p ∈ fieldsOf ctx r) : JS.validLabel p.1 = true := by
  simp only [fieldsOf] at hp
  cases hr : ctx.recs.find r with
  | none => rw [hr] at hp; simp at hp
  | some tfs =>
    rw [hr, Option.getD_some] at hp
    exact List.all_eq_true.mp (labelsOk_spec (hd.labels r tfs hr)).1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- Reading a field the shape test found gives the object's own value. -/
theorem read_found {env jv fs fr l v} (hj : lookup env "j" = some jv) (hjv : jv = .obj fs fr)
    (hl : JS.identShape l = true) (hv : lookup fs l = some v) : JS.evalAtom env (.path "j" [l]) = .ok v := by
  subst hjv
  simp [JS.evalAtom, hl, hj, JS.readPath, JS.readField, hv]

theorem testOf_total {ctx : Ctx} {env jv} (hd : DeclsOk ctx) (t : Ty) (hj : lookup env "j" = some jv)
    (hjv : JS.IsJson jv ∨ jv = .undef) : ∃ b, JS.evalTest env (testOf ctx t) = .ok b := by
  have hroot : JS.evalAtom env (.path "j" []) = .ok jv := by simp [JS.evalAtom, hj, JS.readPath]
  have hne : jv ≠ .untracked := by
    rcases hjv with h | h
    · intro e; subst e; cases h
    · intro e; rw [h] at e; cases e
  cases t with
  | int => exact testField_total .int hroot hne
  | str => exact testField_total .str hroot hne
  | fn a b => exact testField_total (.fn a b) hroot hne
  | entry a b => exact testField_total (.entry a b) hroot hne
  | record r =>
    simp only [testOf]
    let ls := (fieldsOf ctx r).map Prod.fst
    have hshape : JS.evalTest env (.isShape (.path "j" []) ls) = JS.isShapeVal ls jv := by
      simp only [JS.evalTest, evalTest_atom hroot]
    cases hs : JS.isShapeVal ls jv with
    | error e => cases jv <;> simp [JS.isShapeVal] at hs hne
    | ok b =>
      cases b with
      | false => exact ⟨false, foldl_and_false _ (by rw [hshape, hs])⟩
      | true =>
        refine foldl_and_total _ (by rw [hshape, hs]) (fun p hp => ?_)
        cases jv with
        | obj fs fr =>
          simp only [JS.isShapeVal, Except.ok.injEq, Bool.and_eq_true, List.all_eq_true] at hs
          have hfound := hs.2 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
          cases hl : lookup fs p.1 with
          | none => rw [hl] at hfound; cases hfound
          | some v =>
            have hread := read_found hj rfl (label_shape (fieldsOf_label hd hp)) hl
            have hvj : JS.IsJson v := by
              rcases hjv with hjson | hjson
              · cases hjson with
                | obj _ hall => exact hall p.1 v hl
              · cases hjson
            exact testField_total p.2 hread (by intro e; subst e; cases hvj)
        | _ => simp [JS.isShapeVal] at hs

theorem testOf_true {ctx : Ctx} {env jv} (hd : DeclsOk ctx) (t : Ty) (ht : TyOk ctx.recs t)
    (hj : lookup env "j" = some jv) (h : JS.evalTest env (testOf ctx t) = .ok true) :
    ∃ w, JS.evalExpr 1 env (buildOf ctx t) = .ok w ∧ DataOf ctx.recs w t := by
  have hroot : JS.evalAtom env (.path "j" []) = .ok jv := by simp [JS.evalAtom, hj, JS.readPath]
  have hplain : ∀ t', testOf ctx t' = testField t' (.path "j" []) → buildOf ctx t' = .atom (.path "j" []) →
      JS.evalTest env (testOf ctx t') = .ok true → ∃ w, JS.evalExpr 1 env (buildOf ctx t') = .ok w ∧ DataOf ctx.recs w t' := by
    intro t' htest hbuild h'
    rw [htest] at h'
    exact ⟨jv, by rw [hbuild]; simpa [JS.evalExpr] using hroot, testField_true t' hroot h'⟩
  cases t with
  | int => exact hplain .int rfl rfl h
  | str => exact hplain .str rfl rfl h
  | fn a b => exact hplain (.fn a b) rfl rfl h
  | entry a b => exact hplain (.entry a b) rfl rfl h
  | record r =>
    obtain ⟨tfs, hr⟩ := record_declared ht
    have hf : fieldsOf ctx r = tfs := by simp [fieldsOf, hr]
    obtain ⟨htvalid, htnodup⟩ := labelsOk_spec (hd.labels r tfs hr)
    simp only [testOf, hf] at h
    obtain ⟨hshape, hfields⟩ := foldl_and_true _ h
    simp only [JS.evalTest, evalTest_atom hroot] at hshape
    cases jv with
    | obj fs fr =>
      simp only [JS.isShapeVal, Except.ok.injEq, Bool.and_eq_true, List.all_eq_true] at hshape
      -- every declared field is there, and passes its test
      have hfield : ∀ l τl, (l, τl) ∈ tfs → ∃ v, JS.evalAtom env (.path "j" [l]) = .ok v ∧ DataOf ctx.recs v τl := by
        intro l τl hm
        have hfound := hshape.2 l (List.mem_map.mpr ⟨(l, τl), hm, rfl⟩)
        cases hl : lookup fs l with
        | none => rw [hl] at hfound; cases hfound
        | some v =>
          have hread := read_found hj rfl (label_shape (List.all_eq_true.mp htvalid l (List.mem_map.mpr ⟨(l, τl), hm, rfl⟩))) hl
          exact ⟨v, hread, testField_true τl hread (hfields (l, τl) hm)⟩
      let efs := tfs.map fun (p : String × Ty) => (p.1, JS.Atom.path "j" [p.1])
      have hkeys₁ : efs.map Prod.fst = tfs.map Prod.fst := by simp [efs]
      obtain ⟨vs, hvs, hkeys, hq⟩ := evalFields_ok (env := env)
        (Q := fun l v => ∃ τ', lookup tfs l = some τ' ∧ DataOf ctx.recs v τ') efs
        (fun l a hm => by
          obtain ⟨⟨l', τl⟩, hm', he⟩ := List.mem_map.mp hm
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨v, hv, hvt⟩ := hfield l' τl hm'
          exact ⟨v, hv, τl, lookup_of_mem htnodup hm', hvt⟩)
      refine ⟨.obj vs true, ?_, DataOf.obj hr (fun l => ?_) (fun l v τ' hv hτ' => ?_)⟩
      · have hv' : (efs.map Prod.fst).all JS.validLabel = true := by rw [hkeys₁]; exact htvalid
        have hn' : (efs.map Prod.fst).Nodup := by rw [hkeys₁]; exact htnodup
        simp only [buildOf, hf]
        exact evalExpr_obj hv' hn' hvs
      · exact lookup_isSome_keys (hkeys.trans hkeys₁)
      · obtain ⟨τ'', h₁, h₂⟩ := hq l v hv
        rw [hτ'] at h₁; cases h₁; exact h₂
    | _ => simp [JS.isShapeVal] at hshape

theorem parseBody_static {ctx : Ctx} (hd : DeclsOk ctx) (t : Ty) : JS.staticOk (parseBody ctx t) = true := by
  have hj : JS.validIdent "j" = true := by decide +kernel
  have hk : JS.validIdent "k" = true := by decide +kernel
  have hf : JS.validIdent "f" = true := by decide +kernel
  have hfield : ∀ (t' : Ty) (ls : List String), ls.all JS.identShape = true → JS.testOk (testField t' (.path "j" ls)) = true := by
    intro t' ls hls
    cases t' <;> simp [testField, never, JS.testOk, JS.atomOk, hj, hls]
  have htest : JS.testOk (testOf ctx t) = true := by
    cases t with
    | record r =>
      simp only [testOf]
      refine foldl_and_testOk _ ?_ (fun p hp => hfield p.2 [p.1] (by simp [label_shape (fieldsOf_label hd hp)]))
      simp only [JS.testOk, JS.atomOk, hj, List.all_nil, Bool.and_true, Bool.true_and, List.all_eq_true]
      intro l hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      exact fieldsOf_label hd hp
    | _ => simp only [testOf]; exact hfield _ [] rfl
  have hbuild : JS.staticOk (buildOf ctx t) = true := by
    cases t with
    | record r =>
      simp only [buildOf, JS.staticOk, Bool.and_eq_true, List.all_eq_true]
      constructor
      · intro l hl
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact fieldsOf_label hd hp
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        simp [JS.atomOk, hj, label_shape (fieldsOf_label hd hp)]
    | _ => simp [buildOf, JS.staticOk, JS.atomOk, hj]
  simp [parseBody, JS.staticOk, JS.atomOk, htest, hbuild, hk, hf]

theorem parseFn_eval {ctx : Ctx} {env t ok fa okv failv} (hd : DeclsOk ctx)
    (hok : JS.evalAtom env (.path ok []) = .ok okv) (hfail : JS.evalAtom env fa = .ok failv) :
    JS.evalExpr 4 env (.entry (parseFn ctx t ok fa)) =
      .ok (.entryOf (.clos (("f", failv) :: ("k", okv) :: env) "j" (parseBody ctx t))) := by
  have hj : JS.validIdent "j" = true := by decide +kernel
  have hk : JS.validIdent "k" = true := by decide +kernel
  have hf : JS.validIdent "f" = true := by decide +kernel
  have hgj : "j" ∉ JS.emittedGlobals := by decide
  have hgk : "k" ∉ JS.emittedGlobals := by decide
  have hgf : "f" ∉ JS.emittedGlobals := by decide
  have hb := parseBody_static hd t
  simp [parseFn, JS.evalExpr, JS.staticOk, hok, hfail, hj, hk, hf, hgj, hgk, hgf, hb]

theorem entry_valOf {ctx : Ctx} {env t r okv failv} (hd : DeclsOk ctx) (ht : TyOk ctx.recs t) (hr : isData r = true)
    (hokv : ValOf ctx.recs okv (.fn t r)) (hfailv : ValOf ctx.recs failv r) :
    ValOf ctx.recs (.entryOf (.clos (("f", failv) :: ("k", okv) :: env) "j" (parseBody ctx t))) (.entry t r) := by
  simp only [ValOf]
  refine ⟨_, rfl, fun jv hjv => ?_⟩
  have hj : lookup (("j", jv) :: ("f", failv) :: ("k", okv) :: env) "j" = some jv := by simp [lookup]
  have hf : lookup (("j", jv) :: ("f", failv) :: ("k", okv) :: env) "f" = some failv := by simp [lookup]
  have hk : lookup (("j", jv) :: ("f", failv) :: ("k", okv) :: env) "k" = some okv := by simp [lookup]
  obtain ⟨b, hb⟩ := testOf_total hd t hj hjv
  cases b with
  | false =>
    refine ⟨2, failv, ?_, hfailv, (hfailv.dataOf hr).data⟩
    simp [JS.applyVal, parseBody, JS.evalExpr, hb, JS.evalAtom, hf, JS.readPath]
  | true =>
    obtain ⟨w, hw, hwt⟩ := testOf_true hd t ht hj hb
    simp only [ValOf] at hokv
    obtain ⟨ocenv, ox, obody, rfl, H⟩ := hokv
    obtain ⟨n₁, r₁, h₁, hr₁⟩ := H w hwt.valOf
    obtain ⟨M, hM⟩ : ∃ M, max n₁ 1 = M + 1 := ⟨max n₁ 1 - 1, by omega⟩
    refine ⟨M + 3, r₁, ?_, hr₁, (hr₁.dataOf hr).data⟩
    have hw' := JS.evalExpr_mono 1 hw (by simp) (M + 1) (by omega)
    have h₁' := JS.evalExpr_mono n₁ h₁ (by simp) (M + 1) (by omega)
    simp [JS.applyVal, parseBody, JS.evalExpr, hb, JS.evalAtom, hk, JS.readPath, hw', h₁']

/-! ## Declarations -/

theorem resolve_tyOk {ctx} (hd : DeclsOk ctx) : ∀ {tn t}, resolve ctx.types tn = .ok t → TyOk ctx.recs t
  | .int, _, h => by simp only [resolve] at h; cases h; trivial
  | .str, _, h => by simp only [resolve] at h; cases h; trivial
  | .named a, _, h => by
    simp only [resolve] at h
    cases hl : ctx.types.find a with
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

theorem resolveFields_spec {types : Scope Ty} : ∀ (fs : List (String × TyName)) {tfs},
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
      ∃ t, resolve ctx.types rhs = .ok t ∧ ctx'.types = ctx.types.insert a t := by
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
    jd = none ∧ ctx'.vals = ctx.vals ∧ ctx.types.find r = none ∧ labelsOk (fields.map Prod.fst) = true ∧
      ∃ tfs, resolveFields ctx.types fields = .ok tfs ∧ tfs.all (fun p => isData p.2) = true ∧
        ctx'.recs = ctx.recs.insert r tfs ∧ ctx'.types = ctx.types.insert r (.record r) := by
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
            cases hl : ctx.types.find r with
            | none => rfl
            | some _ => simp [hl] at hfresh

theorem declarable_spec {ctx x} (h : declarable ctx x = .ok ()) : JS.bindable x = true ∧ ctx.vals.find x = none := by
  simp only [declarable] at h
  split at h
  · cases h
  · rename_i hv
    split at h
    · cases h
    · rename_i hfresh
      refine ⟨by simpa using hv, ?_⟩
      cases hl : ctx.vals.find x with
      | none => rfl
      | some _ => simp [hl] at hfresh

theorem checkDecl_val {ctx x tn e ctx' jd} (h : checkDecl ctx (.val x tn e) = .ok (ctx', jd)) :
    JS.bindable x = true ∧ ctx.vals.find x = none ∧ ctx'.recs = ctx.recs ∧ ctx'.types = ctx.types ∧
      ∃ τ je, resolve ctx.types tn = .ok τ ∧ checkExpr ctx e τ = .ok je ∧
        ctx'.vals = ctx.vals.insert x τ ∧ jd = some ⟨x, je, isData τ⟩ := by
  simp only [checkDecl] at h
  cases hdc : declarable ctx x with
  | error _ => simp [hdc] at h
  | ok u =>
    cases u
    obtain ⟨hv, hfresh⟩ := declarable_spec hdc
    simp only [hdc] at h
    cases hr : resolve ctx.types tn with
    | error _ => simp [hr] at h
    | ok τ =>
      simp only [hr] at h
      cases hc : checkExpr ctx e τ with
      | error _ => simp [hc] at h
      | ok je =>
        simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hv, hfresh, rfl, rfl, τ, je, rfl, hc, rfl, rfl⟩

theorem checkDecl_entry {ctx x tn ok fail ctx' jd} (h : checkDecl ctx (.entry x tn ok fail) = .ok (ctx', jd)) :
    JS.bindable x = true ∧ ctx.vals.find x = none ∧ x ≠ "then" ∧ ctx'.recs = ctx.recs ∧ ctx'.types = ctx.types ∧
      ∃ t, resolve ctx.types tn = .ok t ∧ isFn t = true ∧ isData (resultTy t) = true ∧
        inferAtom ctx (.var ok) = .ok (.fn (paramTy t) (resultTy t)) ∧ inferAtom ctx fail = .ok (resultTy t) ∧
        ctx'.vals = ctx.vals.insert x (.entry (paramTy t) (resultTy t)) ∧
        jd = some ⟨x, .entry (parseFn ctx (paramTy t) ok (emitAtom fail)), true⟩ := by
  simp only [checkDecl] at h
  cases hdc : declarable ctx x with
  | error _ => simp [hdc] at h
  | ok u =>
    cases u
    obtain ⟨hv, hfresh⟩ := declarable_spec hdc
    simp only [hdc] at h
    split at h
    · cases h
    · rename_i hthen
      cases hr : resolve ctx.types tn with
      | error _ => simp [hr] at h
      | ok t =>
        simp only [hr] at h
        split at h
        · cases h
        · rename_i htype
          have hfn : isFn t = true := by
            cases h1 : isFn t
            · simp [h1] at htype
            · rfl
          have hrd : isData (resultTy t) = true := by
            cases h2 : isData (resultTy t)
            · simp [h2] at htype
            · rfl
          split at h
          · cases h
          · cases hok : inferAtom ctx (.var ok) with
            | error _ => simp [hok] at h
            | ok tok =>
              simp only [hok] at h
              split at h
              · cases h
              · rename_i hokt
                cases hf : inferAtom ctx fail with
                | error _ => simp [hf] at h
                | ok tf =>
                  simp only [hf] at h
                  split at h
                  · cases h
                  · rename_i hft
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have e₁ : tok = .fn (paramTy t) (resultTy t) := by simpa using hokt
                    have e₂ : tf = resultTy t := by simpa using hft
                    subst e₁ e₂
                    exact ⟨hv, hfresh, by simpa using hthen, rfl, rfl, t, rfl, hfn, hrd, rfl, rfl, rfl, rfl⟩

/-- The invariant carries through the program, declaration by declaration, and every name the module
    exports holds data or an entry. -/
theorem checkFrom_sound : ∀ (p : Program) {ctx ctx' js env}, checkFrom ctx p = .ok (ctx', js) →
    Agrees ctx env → DeclsOk ctx →
    ∃ n env', JS.runFrom n env js = .ok env' ∧ Agrees ctx' env' ∧ DeclsOk ctx' ∧
      ∀ d ∈ js, d.exported = true → ∃ v, lookup env' d.name = some v ∧ JS.Exportable v := by
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
          · rw [hrecs] at hs; rw [htypes, Scope.find_insert]
            by_cases e : a = r'
            · simp [e]
            · simp only [e, if_false]; exact hd.recsTyped r' hs
          · rw [hrecs] at h'; exact hd.labels r' tfs' h'
          · rw [hrecs]; rw [htypes, Scope.find_insert] at h'
            by_cases e : a = a'
            · simp only [e, if_true] at h'; cases h'; exact ht
            · simp only [e, if_false] at h'; exact hd.types a' t' h'
          · rw [hrecs]; rw [hvals] at h'; exact hd.vals y t' h'
          · rw [hrecs] at h' ⊢; exact hd.fields r' tfs' h'
          · rw [hrecs] at h'; exact hd.data r' tfs' h'
          · rw [hvals] at h'; exact hd.idents y t' h'
        | record r fields =>
          obtain ⟨rfl, hvals, hfresh, hlab, tfs, hres, hdata, hrecs, htypes⟩ := checkDecl_record hdec
          have hnorec : ctx.recs.find r = none := by
            cases hl : ctx.recs.find r with
            | none => rfl
            | some _ => have := hd.recsTyped r (by rw [hl]; rfl); rw [hfresh] at this; cases this
          have hmono : ∀ r' tfs', ctx.recs.find r' = some tfs' → ctx₁.recs.find r' = some tfs' := by
            intro r' tfs' hl
            rw [hrecs, Scope.find_insert]
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
          · rw [htypes, Scope.find_insert]
            by_cases e : r = r'
            · simp [e]
            · simp only [e, if_false]
              rw [hrecs, Scope.find_insert] at hs; simp only [e, if_false] at hs
              exact hd.recsTyped r' hs
          · rw [hrecs, Scope.find_insert] at h'
            by_cases e : r = r'
            · simp only [e, if_true] at h'; cases h'; rw [hkeys]; exact hlab
            · simp only [e, if_false] at h'; exact hd.labels r' tfs' h'
          · rw [htypes, Scope.find_insert] at h'
            by_cases e : r = a
            · simp only [e, if_true] at h'; cases h'; subst e
              simp only [TyOk]; rw [hrecs, Scope.find_insert]; simp
            · simp only [e, if_false] at h'; exact TyOk.mono hmono (hd.types a t' h')
          · rw [hvals] at h'; exact TyOk.mono hmono (hd.vals y t' h')
          · rw [hrecs, Scope.find_insert] at h'
            by_cases e : r = r'
            · simp only [e, if_true] at h'; cases h'
              obtain ⟨tn, htn⟩ := hresolved (l, t') (lookup_mem ht')
              exact TyOk.mono hmono (resolve_tyOk hd htn)
            · simp only [e, if_false] at h'; exact TyOk.mono hmono (hd.fields r' tfs' h' l t' ht')
          · rw [hrecs, Scope.find_insert] at h'
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
            · rw [hrecs]; rw [hvals, Scope.find_insert] at h'
              by_cases e' : x = y
              · simp only [e', if_true] at h'; cases h'; exact hτ
              · simp only [e', if_false] at h'; exact hd.vals y t' h'
            · rw [hrecs] at h' ⊢; exact hd.fields r' tfs' h'
            · rw [hrecs] at h'; exact hd.data r' tfs' h'
            · rw [hvals, Scope.find_insert] at h'
              by_cases e' : x = y
              · subst e'; exact hident
              · simp only [e', if_false] at h'; exact hd.idents y t' h'
          obtain ⟨n₂, env', hrun, ha', hd', hexp⟩ := ih hrest ha₁ hd₁
          refine ⟨max n₁ n₂, env', ?_, ha', hd', fun d hdm hdx => ?_⟩
          · -- An exported value is data, which can't be called, so the module never exports a callable then.
            have hno : (isData τ && (x == "then") && JS.callable v) = false := by
              cases hdt : isData τ
              · rfl
              · simp [(hvt.dataOf hdt).not_callable]
            simp only [JS.runFrom, hident, hglobal, Bool.not_true, Bool.false_eq_true, if_false, hnot]
            rw [JS.evalExpr_mono n₁ hv (by simp) _ (Nat.le_max_left _ _)]
            simp only [hno, Bool.false_eq_true, if_false]
            exact JS.runFrom_mono _ hrun (by simp) _ (Nat.le_max_right _ _)
          · simp only [List.mem_cons] at hdm
            rcases hdm with rfl | hdm
            · exact ⟨v, JS.runFrom_keeps js' hrun (by simp [lookup_cons]), .data (hvt.dataOf hdx).data⟩
            · exact hexp d hdm hdx
        | entry x tn ok fail =>
          obtain ⟨hvalid, hfreshv, hthen, hrecs, htypes, t, hres, hfn, hrd, hok, hfail, hvals, rfl⟩ := checkDecl_entry hdec
          have ht : TyOk ctx.recs t := resolve_tyOk hd hres
          cases t with
          | fn a r =>
            simp only [paramTy, resultTy] at hok hfail hvals hrd ⊢
            simp only [TyOk] at ht
            obtain ⟨okv, hokv, hokvt⟩ := inferAtom_sound hok ha
            obtain ⟨failv, hfailv, hfailvt⟩ := inferAtom_sound hfail ha
            have hpe := parseFn_eval (ctx := ctx) (t := a) hd hokv hfailv
            have hval := entry_valOf (env := env) hd ht.1 hrd hokvt hfailvt
            have hnot : (lookup env x).isSome = false := by rw [← ha.1 x, hfreshv]; rfl
            have hident : JS.validIdent x = true := by simp only [JS.bindable, Bool.and_eq_true] at hvalid; exact hvalid.1
            have hglobal : JS.emittedGlobals.contains x = false := by
              simp only [JS.bindable, Bool.and_eq_true, Bool.not_eq_true'] at hvalid; exact hvalid.2
            have ha₁ : Agrees ctx₁ ((x, .entryOf (.clos (("f", failv) :: ("k", okv) :: env) "j" (parseBody ctx a))) :: env) := by
              have := agrees_cons (x := x) ha hval
              unfold Agrees at this ⊢
              rw [hvals, hrecs]; exact this
            have hd₁ : DeclsOk ctx₁ := DeclsOk.declare hd hrecs htypes hvals (by simp only [TyOk]; exact ht) hident
            obtain ⟨n₂, env', hrun, ha', hd', hexp⟩ := ih hrest ha₁ hd₁
            refine ⟨max 4 n₂, env', ?_, ha', hd', fun d hdm hdx => ?_⟩
            · have hno : (x == "then") = false := by simpa using hthen
              simp only [JS.runFrom, hident, hglobal, Bool.not_true, Bool.false_eq_true, if_false, hnot]
              rw [JS.evalExpr_mono 4 hpe (by simp) _ (Nat.le_max_left _ _)]
              simp only [hno, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false]
              exact JS.runFrom_mono _ hrun (by simp) _ (Nat.le_max_right _ _)
            · simp only [List.mem_cons] at hdm
              rcases hdm with rfl | hdm
              · exact ⟨.entryOf (.clos (("f", failv) :: ("k", okv) :: env) "j" (parseBody ctx a)),
                  JS.runFrom_keeps js' hrun (by simp [lookup_cons]), .entry⟩
              · exact hexp d hdm hdx
          | _ => simp [isFn] at hfn

/-- **Soundness.** If the compiler accepts a program, the module it emits runs without an error, given
    enough fuel; every name the checker declared holds a value of its declared type, which for an entry
    says what its parse does with anything `JSON.parse` returns; and every name the module exports holds
    data or an entry, never another function. -/
theorem compile_sound {p : Program} {out : JS.Program} (h : compile p = .ok out) :
    ∃ ctx env, check p = .ok (ctx, out) ∧ (∃ n, JS.run n out = .ok env) ∧
      (∀ x τ, ctx.vals.find x = some τ → ∃ v, lookup env x = some v ∧ ValOf ctx.recs v τ) ∧
      ∀ d ∈ out, d.exported = true → ∃ v, lookup env d.name = some v ∧ JS.Exportable v := by
  simp only [compile] at h
  cases hc : check p with
  | error _ => simp [hc] at h
  | ok res =>
    obtain ⟨ctx, js⟩ := res
    simp only [hc, Except.ok.injEq] at h; subst h
    obtain ⟨n, env, hrun, ha, _, hexp⟩ := checkFrom_sound p (env := []) hc
      ⟨fun _ => by simp [Ctx.empty, Scope.find_empty, lookup], fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h⟩
      ⟨fun _ h => by simp [Ctx.empty, Scope.find_empty] at h, fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h,
       fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h, fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h,
       fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h, fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h,
       fun _ _ h => by simp [Ctx.empty, Scope.find_empty] at h⟩
    exact ⟨ctx, env, rfl, ⟨n, hrun⟩, ha.2, hexp⟩

/-- The names the program declares as values or entries. -/
def valNames : Program → List String
  | [] => []
  | .val x _ _ :: ds => x :: valNames ds
  | .entry x _ _ _ :: ds => x :: valNames ds
  | _ :: ds => valNames ds

/-- Checking more declarations never forgets a value. -/
theorem checkFrom_keeps : ∀ (p : Program) {ctx ctx' js}, checkFrom ctx p = .ok (ctx', js) →
    ∀ x, (ctx.vals.find x).isSome → (ctx'.vals.find x).isSome := by
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
          rw [hvals, Scope.find_insert]
          by_cases e : y = x
          · simp [e]
          · simp only [e, if_false]; exact hx
        | entry y tn ok fail =>
          obtain ⟨_, _, _, _, _, t, _, _, _, _, _, hvals, _⟩ := checkDecl_entry hd
          rw [hvals, Scope.find_insert]
          by_cases e : y = x
          · simp [e]
          · simp only [e, if_false]; exact hx

/-- Every value the program declares is one the checker declared, so `compile_sound` covers every
    name in the source. -/
theorem checkFrom_declares : ∀ (p : Program) {ctx ctx' js}, checkFrom ctx p = .ok (ctx', js) →
    ∀ x, x ∈ valNames p → (ctx'.vals.find x).isSome := by
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
            exact checkFrom_keeps ds hrest x (by rw [hvals]; simp [Scope.find_insert])
          · exact ih hrest x hx
        | entry y tn ok fail =>
          simp only [valNames, List.mem_cons] at hx
          rcases hx with rfl | hx
          · obtain ⟨_, _, _, _, _, t, _, _, _, _, _, hvals, _⟩ := checkDecl_entry hd
            exact checkFrom_keeps ds hrest x (by rw [hvals]; simp [Scope.find_insert])
          · exact ih hrest x hx

/-- `compile_sound` is the statement `Counterexamples.lean` refutes for a compiler missing a
    load-bearing check. -/
theorem compile_sound_conclusion : ∀ {p : Program} {out : JS.Program}, compile p = .ok out → Conclusion p out :=
  fun h => compile_sound h

#print axioms compile_sound
#print axioms checkFrom_declares

end LScript
