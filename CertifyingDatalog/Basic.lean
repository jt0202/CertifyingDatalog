import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic


def List.toSet {A: Type} (l: List A): Set A :=
  match l with
  | [] => ∅
  | hd::tl => {hd} ∪ tl.toSet

lemma List.toSet_mem {A: Type} (a:A) (l: List A): a ∈ l ↔ a ∈ l.toSet := by
  induction l with
  | nil =>
    unfold List.toSet
    simp
  | cons hd tl ih =>
    unfold List.toSet
    simp
    rw [ih]

def List.map_except_unit {A B: Type} (l: List A) (f: A → Except B Unit): Except B Unit :=
  match l with
  | [] => Except.ok ()
  | hd::tl =>
    match f hd with
    | Except.ok () => List.map_except_unit tl f
    | Except.error b => Except.error b

lemma List.map_except_unitIsUnitIffAll {A B: Type} (l: List A) (f: A → Except B Unit): List.map_except_unit l f = Except.ok () ↔ ∀ (a:A), a ∈ l → f a = Except.ok () :=
by
  induction l with
  | nil =>
    simp
    unfold List.map_except_unit
    rfl
  | cons hd tl ih =>
    unfold List.map_except_unit
    simp
    cases f hd with
    | ok u =>
      simp
      rw [ih]
    | error e =>
      simp

def List.eraseAll {A: Type} [DecidableEq A] (l: List A) (a:A):List A :=
  match l with
  | [] => []
  | hd::tl => if a = hd
              then List.eraseAll tl a
              else hd::(List.eraseAll tl a)


lemma List.mem_eraseAll {A: Type} [DecidableEq A] (l: List A) (a b:A): a ∈ List.eraseAll l b ↔ a ∈ l ∧ ¬ a = b :=
by
  induction l with
  | nil =>
    unfold List.eraseAll
    simp
  | cons hd tl ih =>
    unfold List.eraseAll
    by_cases hd_b: b = hd
    simp [hd_b]
    rw [← hd_b]
    rw [ih]
    simp
    intro h
    constructor
    intro p
    right
    exact p
    intro p
    cases p with
    | inl p =>
      exfalso
      exact absurd p h
    | inr p =>
      exact p

    simp [hd_b]
    rw [ih]
    constructor
    intro h
    cases h with
    | inl h =>
      constructor
      left
      apply h
      rw [h]
      apply Ne.symm
      simp [hd_b]
    | inr h =>
      constructor
      right
      simp [h]
      simp [h]

    intro h
    rcases h with ⟨left,right⟩
    cases left with
    | inl h' =>
      left
      apply h'
    | inr h' =>
      right
      constructor
      apply h'
      apply right



def List.diff' {A: Type} [DecidableEq A] (l1 l2: List A) : List A :=
  match l2 with
  | [] => l1
  | hd::tl => List.diff' (List.eraseAll l1 hd) tl

lemma List.mem_diff' {A: Type} [DecidableEq A] (l1 l2: List A) (a: A): a ∈ List.diff' l1 l2 ↔ a ∈ l1 ∧ ¬ a ∈ l2 :=
by
  induction l2 generalizing l1 with
  | nil =>
    unfold List.diff'
    simp
  | cons hd tl ih =>
    unfold List.diff'
    simp
    rw [ih]
    rw [List.mem_eraseAll]
    tauto

lemma List.diff'_empty {A: Type} [DecidableEq A] (l1 l2: List A): List.diff' l1 l2 = [] ↔ ∀ (a:A), a ∈ l1 → a ∈ l2 := by
  induction l2 generalizing l1 with
  | nil =>
    unfold diff'
    constructor
    intro h a
    rw [h]
    simp

    cases l1 with
    | nil =>
      simp
    | cons hd tl =>
      simp

  | cons hd tl ih =>
    constructor
    intros h
    unfold diff' at h
    intro a a_l1
    by_cases a_hd: a = hd
    rw [a_hd]
    simp

    simp
    right
    specialize ih (eraseAll l1 hd)
    apply Iff.mp ih
    apply h
    rw [List.mem_eraseAll]
    constructor
    apply a_l1
    apply a_hd

    intro h
    unfold diff'
    rw [ih]
    intro a a_erase
    rw [List.mem_eraseAll] at a_erase
    rcases a_erase with ⟨a_l1, a_hd⟩
    specialize h a a_l1
    simp at h
    simp [a_hd] at h
    apply h

def List.map_except.go {A B C: Type} (f: A → Except B C) (l: List A) (curr: List C): Except B (List C) :=
  match l with
  | nil => Except.ok curr
  | cons hd tl =>
    match f hd with
    | Except.ok c =>
      List.map_except.go f tl  (curr.append [c])
    | Except.error msg =>
      Except.error msg

def List.map_except {A B C: Type} (f: A → Except B C) (l: List A): Except B (List C) := List.map_except.go f l []

lemma List.map_except_go_ok_length {A B C: Type} (f: A → Except B C) (l1: List A) (curr l2: List C) (h: List.map_except.go f l1 curr = Except.ok l2):
  List.length l1 + List.length curr = List.length l2 :=
  by
    induction l1 generalizing curr with
    | nil =>
      unfold map_except.go at h
      simp at h
      rw [h]
      simp
    | cons hd tl ih =>
      unfold map_except.go at h
      simp at h
      cases p:f hd with
      | error e =>
        simp [p] at h
      | ok c =>
        simp [p] at h
        specialize ih (curr ++ [c]) h
        rw [← ih]
        simp
        rw [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm (m:= 1)]

def List.foldl_union {A B: Type} [DecidableEq B]  (f: A → Finset B) (init: Finset B) (l: List A): Finset B := List.foldl (fun x y => x ∪ f y) init l

lemma List.mem_foldl_union {A B: Type} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B) (b:B): b ∈ List.foldl_union f init l ↔ b ∈ init ∨ ∃ (a:A), a ∈ l ∧ b ∈ f a :=
by
  unfold foldl_union
  induction l generalizing init with
  | nil =>
    simp
  | cons hd tl ih =>
    simp
    rw [ih]
    simp
    tauto

lemma List.subset_foldl_union {A B: Type} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B): init ⊆ List.foldl_union f init l := by
  unfold foldl_union
  induction l generalizing init with
  | nil =>
    simp
  | cons hd tl ih =>
    simp
    apply Finset.Subset.trans (s₂ := init ∪ f hd)
    rw [Finset.subset_iff]
    intro x x_mem
    simp
    left
    apply x_mem
    apply ih



lemma List.subset_result_foldl_union {A B: Type} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B) (a:A) (mem: a ∈ l): f a ⊆ List.foldl_union f init l := by
  unfold foldl_union
  induction l generalizing init with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    simp at mem
    simp
    cases mem with
    | inl a_hd =>
      rw [a_hd]
      apply Finset.Subset.trans (s₂ := init ∪ f hd)
      rw [Finset.subset_iff]
      intro x x_mem
      simp
      right
      apply x_mem
      apply subset_foldl_union
    | inr a_tl =>
      apply ih
      exact a_tl


lemma List.foldl_union_empty {A B: Type} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B):List.foldl_union f init l = ∅ ↔ init = ∅ ∧ ∀ (a:A), a ∈ l → f a = ∅ := by
  unfold List.foldl_union
  induction l generalizing init with
  | nil =>
    simp
  | cons hd tl ih =>
    simp
    rw [ih]
    rw [Finset.union_eq_empty]
    tauto

lemma List.foldl_union_subset_set {A B: Type} [DecidableEq B] (l: List A) (f: A → Finset B) (init: Finset B) (S: Set B): ↑( List.foldl_union f init l) ⊆ S ↔ ↑init ⊆ S ∧ ∀ (a:A), a ∈ l → ↑ (f a) ⊆ S:= by
  unfold foldl_union
  induction l generalizing init with
  | nil =>
    simp
  | cons hd tl ih =>
    simp
    rw [ih]
    simp
    tauto

lemma Array.mem_iff_get (a:A) (as: Array A): a ∈ as ↔ ∃ (i:ℕ) (h: i < as.size), as.get (Fin.mk i h) = a := by
  rw [Array.mem_def, List.mem_iff_get]
  constructor
  · intro h
    rcases h with ⟨n, get_n⟩
    use n.val
    use n.isLt
    unfold get
    apply get_n
  · intro h
    rcases h with ⟨i, hi, get_i⟩
    use (Fin.mk i hi)
    unfold get at get_i
    exact get_i

-- added based on https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/finset.2Efilter
noncomputable def Finset.filter_nc (p: A → Prop) (S: Finset A):= @Finset.filter A p (Classical.decPred p) S

lemma Finset.mem_filter_nc (a:A) (p: A → Prop) (S: Finset A): a ∈ Finset.filter_nc p S ↔ p a ∧ a ∈ S :=
by
  unfold filter_nc
  have dec: DecidablePred p := Classical.decPred p
  simp [Finset.mem_filter]
  rw [And.comm]
