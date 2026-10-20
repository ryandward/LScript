/-!
# Scopes: maps from names, as tries

The checker looks names up as it checks, and `certify/check.sh` has Lean's kernel run the checker. In
an association list, a lookup compares the name with every name before it, and comparing strings is
slow for the kernel, so a program's lookups cost it time and memory quadratic in the program's length.
A `Scope` is a trie over character codes instead: finding a name costs the kernel the length of the
name, in comparisons of numbers, which it holds natively. `Scope.find_insert` is the one fact the
proof needs about it.
-/

namespace LScript

/-- A trie over character codes. A node holds one character, the value whose key ends there, the trie
    of what follows it, and its next sibling. -/
inductive Trie (α : Type) where
  | leaf
  | node (c : Nat) (here : Option α) (kids : Trie α) (sibs : Trie α)

namespace Trie

variable {α : Type}

/-- The value ending at character `k`, and the trie after it: nothing, if no sibling holds `k`. -/
def child (k : Nat) : Trie α → Option α × Trie α
  | .leaf => (none, .leaf)
  | .node c here kids sibs => if c = k then (here, kids) else child k sibs

/-- The trie with what `child k` gives replaced by `f` of it, adding a sibling for `k` if there is
    none. -/
def modify (k : Nat) (f : Option α × Trie α → Option α × Trie α) : Trie α → Trie α
  | .leaf => .node k (f (none, .leaf)).1 (f (none, .leaf)).2 .leaf
  | .node c here kids sibs =>
    if c = k then .node c (f (here, kids)).1 (f (here, kids)).2 sibs
    else .node c here kids (modify k f sibs)

def find : List Nat → Trie α → Option α
  | [], _ => none
  | [k], t => (t.child k).1
  | k :: k' :: ks, t => find (k' :: ks) (t.child k).2

def insert : List Nat → α → Trie α → Trie α
  | [], _, t => t
  | [k], a, t => t.modify k fun p => (some a, p.2)
  | k :: k' :: ks, a, t => t.modify k fun p => (p.1, insert (k' :: ks) a p.2)

theorem child_modify_same (k : Nat) (f : Option α × Trie α → Option α × Trie α) :
    ∀ t : Trie α, (t.modify k f).child k = f (t.child k)
  | .leaf => by simp [modify, child]
  | .node c here kids sibs => by
    by_cases h : c = k
    · subst h; simp [modify, child]
    · simp [modify, child, h, child_modify_same k f sibs]

theorem child_modify_other {k k' : Nat} (hk : k ≠ k') (f : Option α × Trie α → Option α × Trie α) :
    ∀ t : Trie α, (t.modify k f).child k' = t.child k'
  | .leaf => by simp [modify, child, hk]
  | .node c here kids sibs => by
    by_cases h : c = k
    · subst h; simp [modify, child, hk]
    · simp only [modify, child, h, if_false, child_modify_other hk f sibs]

theorem find_leaf : ∀ ks : List Nat, find ks (.leaf : Trie α) = none
  | [] => rfl
  | [_] => rfl
  | _ :: k' :: ks => find_leaf (k' :: ks)

theorem find_insert {a : α} : ∀ (ks : List Nat), ks ≠ [] → ∀ (ks' : List Nat) (t : Trie α),
    find ks' (insert ks a t) = if ks = ks' then some a else find ks' t
  | [], h, _, _ => absurd rfl h
  | [_], _, [], _ => by simp [find]
  | [k], _, [k'], t => by
    by_cases e : k = k'
    · subst e; simp [find, insert, child_modify_same]
    · simp [find, insert, child_modify_other e, e]
  | [k], _, k' :: k'' :: ks', t => by
    by_cases e : k = k'
    · subst e; simp [find, insert, child_modify_same]
    · simp [find, insert, child_modify_other e, e]
  | _ :: _ :: _, _, [], _ => by simp [find]
  | k :: k₂ :: ks, _, [k'], t => by
    by_cases e : k = k'
    · subst e; simp [find, insert, child_modify_same]
    · simp [find, insert, child_modify_other e, e]
  | k :: k₂ :: ks, _, k' :: k₂' :: ks', t => by
    by_cases e : k = k'
    · subst e
      simp only [find, insert, child_modify_same]
      rw [find_insert (k₂ :: ks) (List.cons_ne_nil _ _) (k₂' :: ks')]
      simp
    · simp [find, insert, child_modify_other e, e]

end Trie

/-- A name's key: a 0, so that no key is empty, then the codes of its characters. -/
def key (s : String) : List Nat := 0 :: s.data.map Char.toNat

theorem key_inj {s t : String} (h : key s = key t) : s = t := by
  have hmap : ∀ (as bs : List Char), as.map Char.toNat = bs.map Char.toNat → as = bs := by
    intro as
    induction as with
    | nil => intro bs h; cases bs with
      | nil => rfl
      | cons _ _ => simp at h
    | cons c cs ih =>
      intro bs h
      cases bs with
      | nil => simp at h
      | cons d ds =>
        simp only [List.map_cons, List.cons.injEq] at h
        have hc : c = d := Char.eq_of_val_eq (UInt32.toNat_inj.mp h.1)
        rw [hc, ih ds h.2]
  simp only [key, List.cons.injEq, true_and] at h
  exact String.ext (hmap _ _ h)

/-- A map from names. -/
structure Scope (α : Type) where
  trie : Trie α

namespace Scope

variable {α : Type}

def empty : Scope α := ⟨.leaf⟩

def find (s : Scope α) (x : String) : Option α := s.trie.find (key x)

def insert (s : Scope α) (x : String) (a : α) : Scope α := ⟨s.trie.insert (key x) a⟩

theorem find_empty (x : String) : (empty : Scope α).find x = none := Trie.find_leaf _

theorem find_insert (s : Scope α) (x y : String) (a : α) :
    (s.insert x a).find y = if x = y then some a else s.find y := by
  simp only [find, insert]
  rw [Trie.find_insert (key x) (List.cons_ne_nil _ _) (key y) s.trie]
  by_cases e : x = y
  · subst e; simp
  · have hk : key x ≠ key y := fun h => e (key_inj h)
    simp [hk, e]

theorem find_foldl (ws : List String) (x : String) :
    ∀ s : Scope Unit, (ws.foldl (fun s w => s.insert w ()) s).find x = if ws.contains x then some () else s.find x := by
  induction ws with
  | nil => intro s; rfl
  | cons w ws ih =>
    intro s
    simp only [List.foldl_cons, ih, find_insert, List.contains_cons]
    by_cases e : w = x
    · subst e; simp
    · have : (x == w) = false := by simp [Ne.symm e]
      simp [e, this]

end Scope

end LScript
