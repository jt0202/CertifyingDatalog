import Batteries.Data.HashMap
import Batteries.Data.AssocList
import Batteries.Classes.BEq
import Mathlib.Data.List.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.AllAny


namespace Batteries
section HashMap
variable {A:Type} [Hashable A] [DecidableEq A] {B: Type} [DecidableEq B]

instance: Batteries.HashMap.LawfulHashable A := {hash_eq := by simp}

instance: PartialEquivBEq A := {symm:= by simp, trans:= by simp}

lemma List.find?_mem_iff (l: List A) (p: A → Bool) (a:A) (unique: List.Pairwise (fun x y => ¬ (p x = true ∧ p y = true)) l): l.find? p = some a ↔ a ∈ l ∧ p a = true := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    unfold List.find?
    by_cases p_hd: p hd = true
    simp [p_hd]
    constructor
    intro hd_a
    constructor
    left
    apply Eq.symm hd_a
    rw [← hd_a]
    exact p_hd
    intro h
    rcases h with ⟨a_mem, p_a⟩
    cases a_mem with
    | inl a_hd =>
      apply Eq.symm a_hd
    | inr a_tl =>
      simp at unique
      rcases unique with ⟨unique, _⟩
      specialize unique a a_tl p_hd
      rw [unique] at p_a
      contradiction

    simp [p_hd]
    rw [ih]
    aesop
    aesop

lemma Array.get_set_not_eq (as: Array A) (i: Fin as.size) (j : Nat) (hj : j < as.size) (v : A) (i_j: ¬ j = i.val): (as.set i v)[j]'(by simp [*]) = as[j] := by
  rw [Array.get_set]
  simp
  intro h
  simp_rw[h] at i_j
  simp at i_j
  exact hj

lemma Array.mem_iff_exists (as: Array A) (a:A): a ∈ as ↔ ∃ (i: Fin as.size), a = as[i] :=
by
  cases as with
  | mk l  =>
    rw [Array.mem_def]
    simp
    rw [List.mem_iff_get]
    constructor
    intro h
    rcases h with ⟨n, get_n⟩
    use n
    apply Eq.symm
    apply get_n

    intro h
    rcases h with ⟨i, get_i⟩
    use i
    apply Eq.symm
    apply get_i

lemma List.mem_set (l: List A)(i: Fin l.length) (a d: A): a ∈ l.set i d ↔ a = d ∨ ∃ (j: Fin l.length), j ≠ i ∧ a = l[j] := by
  simp
  induction l with
  | nil =>
    exfalso
    simp at i
    have h: i.val < 0 := i.isLt
    simp at h
  | cons hd tl ih =>
    cases hi: i.val with
    | zero =>
      simp
      rw [List.mem_iff_get]
      constructor
      intro h
      cases h with
      | inl a_d =>
        left
        apply a_d
      | inr get_a =>
        rcases get_a with ⟨k, get_a⟩
        right
        have isLt_k: Nat.succ k.val < (hd::tl).length := by simp
        use Fin.mk (Nat.succ k.val) isLt_k
        constructor
        cases i with
        | mk i_val isLt_i =>
          simp
          simp at hi
          rw [hi]
          simp
        rw [← get_a]
        rw [← List.get_cons_succ (a:=hd)]

      intro h
      cases h with
      | inl ad =>
        left;apply ad
      | inr h =>
        rcases h with ⟨j, j_i, get_j⟩
        right
        cases hj:j.val with
        | zero =>
          rw [← Ne.eq_def, ← Fin.val_ne_iff, hj, hi] at j_i
          simp at j_i
        | succ k =>
          have isLt_k: k < tl.length := by
            rw [← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, ← hj]
            apply j.isLt
          use Fin.mk k isLt_k
          rw [get_j]
          have hj': j = Fin.mk k.succ (by simp [isLt_k]) := by
            rw [Fin.ext_iff]
            simp
            apply hj
          rw [hj', List.get_cons_succ]
    | succ m =>
      rw [List.set_succ]
      simp
      have isLt_m: m < tl.length := by
        rw [← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, ← hi]
        apply i.isLt
      specialize ih (Fin.mk m isLt_m)
      rw [ih]
      constructor
      intro h
      cases h with
      | inl ahd =>
        right
        use 0
        simp [ahd]
        rw [← Ne.eq_def, ← Fin.val_ne_iff]
        simp [Fin.ext, hi]
      | inr h =>
        cases h with
        | inl ad =>
          left;apply ad
        | inr h =>
          rcases h with ⟨j,j_i, get_j⟩
          right
          have isLt_j: j.val.succ < (hd::tl).length := by simp
          use Fin.mk j.val.succ isLt_j
          constructor
          rw [← Ne.eq_def, ← Fin.val_ne_iff]
          simp
          rw [hi]
          rw [← Ne.eq_def, Nat.succ_ne_succ]
          rw [← Ne.eq_def, ← Fin.val_ne_iff] at j_i
          simp at j_i
          rw [Ne.eq_def]
          apply j_i

          simp
          apply get_j


      intro h
      cases h with
      | inl ad =>
        right;left;apply ad
      | inr h =>
        rcases h with ⟨j, j_i, get_j⟩
        cases hj: j.val with
        | zero =>
          left
          rw [get_j]
          have j_zero: j = 0 := by
            rw [Fin.ext_iff]
            apply hj
          rw [j_zero, List.get_cons_zero]
        | succ n =>
          right
          right
          have isLt_n: n < tl.length := by
            rw [← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one, ← hj]
            apply j.isLt
          use Fin.mk n isLt_n
          simp
          constructor
          rw [← Ne.eq_def, ← Nat.succ_ne_succ, Nat.succ_eq_add_one, ← hj, Nat.succ_eq_add_one, ← hi]
          rw [Fin.val_ne_iff]
          apply j_i
          have isLt_succ_n: n + 1 < (hd::tl).length := by simp; apply isLt_n
          rw [get_j, ← List.get_cons_succ (a:=hd) (h:= isLt_succ_n)]
          congr
          rw [Fin.ext_iff]
          simp [hj]


lemma List.replaceF_distinct_mem (l: List (A × B)) (dist: List.Pairwise (fun x y => ¬ x.1 = y.1) l) (a: A) (ab ab': A × B) (mem: ∃ (c: A × B), c ∈ l ∧ c.1 = a): ab ∈  List.replaceF (fun x => if x.1 == a then some ab' else none) l ↔ (ab ∈ l ∧ ab.1 ≠ a) ∨ ab = ab' := by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold List.replaceF
    simp
    by_cases hd_a: hd.1 = a
    simp [hd_a]
    by_cases ab_a: ab.1 = a
    have ab_tl: ¬ ab ∈ tl := by
      simp at dist
      rcases dist with ⟨dist, _⟩
      specialize dist ab.1 ab.2
      simp at dist
      by_contra ab_tl
      specialize dist ab_tl
      rw [← ab_a] at hd_a
      contradiction
    simp [ab_a, ab_tl]

    simp[ab_a]
    have ab_hd: ¬ ab = hd := by
      by_contra h
      rw [h] at ab_a
      contradiction
    simp [ab_hd]
    tauto

    simp [hd_a]
    rw [List.pairwise_cons] at dist
    rcases dist with ⟨_, tl_dist⟩
    specialize ih tl_dist
    have mem': (∃ c ∈ tl, c.1 = a) := by
      rcases mem with ⟨c, c_mem, c_a⟩
      simp at c_mem
      have c_hd: ¬ c = hd := by
        by_contra p
        rw [p] at c_a
        contradiction
      simp [c_hd] at c_mem
      use c
    specialize ih mem'
    simp at ih
    rw [ih]

    rw [← or_assoc, or_and_left]
    have h: (ab = hd ∨ ¬ab.1 = a) ↔ ¬ ab.1 = a := by
      constructor
      intro h
      cases h with
      | inl h =>
        rw [h]
        apply hd_a
      | inr h =>
        apply h
      tauto
    rw [h]


lemma Array.mem_set (as: Array A) (i: Fin as.size) (a d: A): a ∈ as.set i d ↔ a = d ∨ ∃ (j: Fin as.size), j ≠ i ∧ a = as[j] :=
by
  cases as with
  | mk data =>
    unfold Array.set
    rw [Array.mem_def]
    simp
    rw [List.mem_set]
    tauto

lemma Array.foldl_union (as: Array A) (f: A → Finset B) (S: Finset B) (b: B):  b ∈ (Array.foldl (fun x y => x ∪ f y) S as) ↔ b ∈ S ∨ ∃ (a: A), a ∈ as ∧ b ∈ f a :=
by
  simp [Array.foldl_eq_foldl_data, Array.mem_def]
  cases as with
  | mk data =>
    simp
    induction data generalizing S with
    | nil =>
      simp
    | cons hd tl ih =>
      unfold List.foldl
      rw [ih]
      simp
      tauto


lemma Array.get_mem (as: Array A) (i: Fin as.size): as[i] ∈ as :=
by
  rw [Array.mem_def]
  apply Array.getElem_mem_data

lemma AssocList.eq_iff_toList (l1 l2: AssocList A B): l1 = l2 ↔ l1.toList = l2.toList :=
by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp
    | cons hda hdb tl =>
      simp
  | cons hda hdb tl ih =>
    cases l2 with
    | nil =>
      simp
    | cons hda' hdb' tl' =>
      simp
      rw [ih]
      tauto

def AssocList.containsKeyValue (l: AssocList A B) (a: A) (b: B): Bool :=
  match l with
  | nil => false
  | cons hda hdb tl =>
    if a == hda
    then
      if b == hdb
      then true
      else AssocList.containsKeyValue  tl a b
    else AssocList.containsKeyValue  tl a b

lemma AssocList.mem_containsKeyValue_iff_mem_toList (l: AssocList A B) (ab :A × B): AssocList.containsKeyValue l ab.1 ab.2 ↔ ab ∈ l.toList :=
by
  induction l with
  | nil =>
    unfold containsKeyValue
    simp
  | cons hda hdb tl ih =>
    unfold containsKeyValue
    constructor
    intro h
    simp
    by_cases hda_ab: ab.1 = hda
    by_cases hdb_ab: ab.2 = hdb
    left
    ext
    simp[*]
    simp[*]

    simp[hda_ab, hdb_ab] at h
    right
    rw [← ih]
    simp [h, hda_ab]

    simp [hda_ab] at h
    right
    rw [← ih]
    apply h

    -- back direction
    intro h
    unfold toList at h
    simp at h
    by_cases hda_ab: ab.1 = hda
    by_cases hdb_ab: ab.2 = hdb
    simp [hda_ab, hdb_ab]

    simp [hda_ab]
    cases h with
    | inl h =>
      rw [h] at hdb_ab
      simp at hdb_ab
    | inr h =>
      rw [← ih, hda_ab] at h
      simp [h]


    cases h with
    | inl h =>
      rw [h] at hda_ab
      simp at hda_ab
    | inr h =>
      rw [← ih] at h
      simp [h]


instance: DecidableEq (AssocList A B) :=
  fun l1 l2 =>
    match decEq l1.toList l2.toList with
    | isTrue h => isTrue (Iff.mpr (AssocList.eq_iff_toList l1 l2) h)
    | isFalse h => isFalse (Iff.mpr (Iff.ne (AssocList.eq_iff_toList l1 l2)) h)

lemma HashMap.Imp.Buckets.mem_update (buckets: HashMap.Imp.Buckets A B) (i : USize) (d: AssocList A B) (h : USize.toNat i < Array.size buckets.1) (ab: A × B): (∃ (bkt: AssocList A B), bkt ∈ (buckets.update i d h).1 ∧ ab ∈ bkt.toList) ↔ ab ∈ d.toList ∨ ∃ (j: Fin buckets.1.size), j.1 ≠ i.toNat ∧ ab ∈ (buckets.1[j]).toList :=
by
  unfold update
  simp [Array.mem_set]
  constructor
  intro g
  cases g with
  | inl g =>
    left
    apply g
  | inr g =>
    rcases g with ⟨bkt, g, ab_bkt⟩
    rcases g with ⟨j, j_i, bkt_j⟩
    right
    use j
    constructor
    rw [← Ne.eq_def, ← Fin.val_ne_iff] at j_i
    simp at j_i
    apply j_i
    rw [← bkt_j]
    apply ab_bkt

  intro g
  cases g with
  | inl g =>
    left
    apply g
  | inr g =>
    rcases g with ⟨j, j_i, ab_mem⟩
    right
    use buckets.1[j]
    constructor
    use j
    constructor
    rw [← Ne.eq_def, ← Fin.val_ne_iff]
    simp
    apply j_i
    simp
    apply ab_mem

def HashMap.Imp.Buckets.kv (buckets: HashMap.Imp.Buckets A B): Finset (A × B) := Array.foldl (fun x y => x ∪ y.toList.toFinset) ∅ buckets.val

def HashMap.Imp.kv (m: HashMap.Imp A B): Finset (A × B) := m.2.kv


def HashMap.Imp.kv_member (m: HashMap.Imp A B) (a: A) (b:B): Bool :=
  let ⟨_, buckets⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.2 (hash a |>.toUSize)
  let bkt := buckets.1[i]

  bkt.containsKeyValue a b

lemma HashMap.Imp.kv_member_iff_in_kv (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (a: A) (b:B): (a,b) ∈ m.kv ↔ HashMap.Imp.kv_member m a b = true :=
by
  cases m with
  | mk size buckets =>
    unfold Imp.kv
    unfold Imp.Buckets.kv
    rw [Array.foldl_union]
    unfold kv_member
    simp
    rw [HashMap.Imp.WF_iff] at wf
    simp at wf
    constructor
    intro h
    rcases h with ⟨bkt, bkt_mem, ab_mem⟩
    rw [Array.mem_iff_exists] at bkt_mem
    rcases bkt_mem with ⟨i, bkt_i⟩
    have i_eq: i = (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2) := by
      have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val), Batteries.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := by
        rcases wf with ⟨_, wf⟩
        apply wf.hash_self
      specialize hash_self i i.isLt
      unfold AssocList.All at hash_self
      specialize hash_self (a,b)
      rw [bkt_i] at ab_mem
      specialize hash_self ab_mem
      unfold mkIdx
      simp
      rw [Fin.ext_iff, ← hash_self]

    rw [i_eq] at bkt_i
    simp at bkt_i
    rw [← bkt_i]
    rw [← AssocList.mem_containsKeyValue_iff_mem_toList] at ab_mem
    simp at ab_mem
    apply ab_mem

    intro h
    use buckets.1.get (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    simp
    constructor
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    rw [← AssocList.mem_containsKeyValue_iff_mem_toList]
    exact h


def HashMap.Imp.Buckets.keys' (buckets: HashMap.Imp.Buckets A B): Finset A := Array.foldl (fun x y => x ∪ (y.toList.map Prod.fst).toFinset) ∅ buckets.val

lemma HashMap.Imp.Buckets.keys'_iff_kv (buckets: HashMap.Imp.Buckets A B) (a:A): a ∈ buckets.keys' ↔ ∃ (b:B), (a,b) ∈ buckets.kv:= by
  unfold keys'
  unfold kv
  simp_rw [Array.foldl_union]
  simp
  tauto



lemma HashMap.Imp.Buckets.keys'_mem_iff (buckets: HashMap.Imp.Buckets A B) (a:A): a ∈ buckets.keys' ↔ ∃ (l: AssocList A B), l ∈ buckets.val ∧ l.contains a:=
by
  unfold keys'
  rw [Array.foldl_union]
  simp

def HashMap.Imp.keys' (m: HashMap.Imp A B): Finset A :=
  match m with
  | ⟨_, buckets⟩ => buckets.keys'

lemma HashMap.Imp.keys'_iff_kv (m: HashMap.Imp A B) (a:A): a ∈ m.keys' ↔ ∃ (b:B), (a,b) ∈ m.kv:= by
  unfold keys'
  unfold kv
  cases m with
  | mk size buckets =>
    simp
    rw [HashMap.Imp.Buckets.keys'_iff_kv]


lemma HashMap.Imp.contains_iff (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m): m.contains a ↔ a ∈ m.keys' :=
by
  cases m with
  | mk size buckets =>
    unfold contains
    simp only
    constructor
    intro h
    unfold keys'
    simp
    unfold HashMap.Imp.Buckets.keys'
    rw [Array.foldl_union]
    simp
    use buckets.1.get (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    simp
    constructor
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)
    rw [AssocList.contains_eq, List.any_iff_exists] at h
    simp at h
    apply h

    intro h
    unfold keys' at h
    simp at h
    rw [HashMap.Imp.Buckets.keys'_mem_iff] at h
    rcases h with ⟨l, l_buckets, a_l⟩
    rw [Batteries.HashMap.Imp.WF_iff] at wf
    simp at wf
    rcases wf with ⟨_, wf⟩
    rw [Batteries.AssocList.contains_eq, List.any_iff_exists]
    unfold mkIdx
    simp
    rw [Batteries.AssocList.contains_eq, List.any_iff_exists] at a_l
    rcases a_l with ⟨ab, ab_mem, ab_a⟩
    use ab.2
    rw [← Array.contains_def] at l_buckets
    unfold Array.contains at l_buckets
    rw [Array.any_iff_exists] at l_buckets
    rcases l_buckets with ⟨i, _, i_len, l_buckets⟩
    simp at l_buckets

    have i_val : i = USize.toNat (UInt64.toUSize (hash a) % Array.size buckets.val) := by
      have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val),
      Batteries.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := wf.hash_self

      specialize hash_self i.val i_len
      unfold AssocList.All at hash_self
      specialize hash_self ab
      rw [← l_buckets] at hash_self
      specialize hash_self ab_mem
      simp at ab_a
      rw [← ab_a]
      rw [hash_self]

    simp [← i_val, ← l_buckets]
    simp at ab_a
    rw [← ab_a]
    apply ab_mem

lemma splitArrayLemma (as: Array A) (f: A → List B) (i: ℕ) (h: i < as.size) (b:B): (∃ (a:A), a ∈ as ∧ b ∈ f a) ↔( b ∈ f as[i] ∨ ∃ (j: Fin as.size), j.1 ≠ i ∧ b ∈ f as[j]) := by
  constructor
  intro h
  rcases h with ⟨a, a_mem, b_a⟩
  rw [Array.mem_iff_exists] at a_mem
  rcases a_mem with ⟨k, a_k⟩
  by_cases k_i: k = i
  left
  simp [← k_i]
  rw [a_k] at b_a
  apply b_a

  right
  use k
  constructor
  apply k_i
  rw [a_k] at b_a
  apply b_a

  --back
  intro h
  cases h with
  | inl hi =>
    use as[i]
    constructor
    apply Array.get_mem as (Fin.mk i h)
    apply hi
  | inr hj =>
    rcases hj with ⟨j, _, b_j⟩
    use as[j]
    constructor
    apply Array.get_mem
    apply b_j


lemma AssocList.toList_cons (hda: A) (hdb: B) (tl: AssocList A B): AssocList.toList (AssocList.cons hda hdb tl) = (hda, hdb)::AssocList.toList tl := by
  unfold AssocList.toList
  split
  rfl
  next n =>
    simp

lemma foldl_reinsertAux (source:(AssocList A B)) (target: HashMap.Imp.Buckets A B) (ab: A × B): (∃ (bkt: AssocList A B), bkt ∈ (List.foldl (fun d x => HashMap.Imp.reinsertAux d x.1 x.2) target (AssocList.toList source)).1 ∧ ab ∈ bkt.toList ) ↔ (∃ (bkt: AssocList A B),  bkt ∈ target.1 ∧ ab ∈ bkt.toList) ∨ ab ∈ source.toList := by
  induction source generalizing target with
  | nil =>
    unfold List.foldl
    simp
  | cons hda hdb tl ih =>
    unfold List.foldl
    simp
    rw [ih]
    unfold HashMap.Imp.reinsertAux
    simp
    rw [HashMap.Imp.Buckets.mem_update, AssocList.toList_cons]
    simp

    rw [or_assoc (a:= ab = (hda, hdb)), or_comm (a:= (ab = (hda, hdb))), or_assoc (c:= ab ∈ AssocList.toList tl), splitArrayLemma (b:= ab) (f:= AssocList.toList) (as:=target.1) (i:=USize.toNat (HashMap.Imp.mkIdx target.2 (UInt64.toUSize (hash hda)))) (h:= (HashMap.Imp.mkIdx target.2 (UInt64.toUSize (hash hda))).2)]
    simp



lemma HashMap.Imp.expand_go_mem (i : Nat) (source : Array (AssocList A B)) (target : Buckets A B) (ab: A × B): (∃ (bkt: AssocList A B), bkt ∈ (HashMap.Imp.expand.go i source target).1 ∧ ab ∈ bkt.toList) ↔ ∃ (bkt: AssocList A B), (bkt ∈ target.1 ∨ ∃ (j: Fin source.size), j.val ≥ i ∧ bkt = source[j]) ∧ ab ∈ bkt.toList := by
  induction' h:(source.size - i)  with n ih generalizing source i target

  rw [Nat.sub_eq_zero_iff_le] at h
  unfold expand.go
  have if_cond: ¬ i < Array.size source := by
    apply Nat.not_lt_of_le
    apply h
  simp [if_cond]

  constructor
  intro g
  rcases g with ⟨bkt, bkt_mem, ab_mem⟩
  use bkt
  constructor
  left
  apply bkt_mem
  apply ab_mem

  intro g
  rcases g with ⟨bkt, g, ab_mem⟩
  cases g with
  | inl g =>
    use bkt
  | inr g =>
    rcases g with ⟨j, i_le_j, _⟩
    have lt_self: Array.size source < Array.size source := by
      apply Nat.lt_of_le_of_lt (m:=j.val)
      apply Nat.le_trans
      apply h
      apply i_le_j
      apply j.isLt
    simp at lt_self

  --step
  unfold expand.go
  split
  swap
  rename_i h'
  simp at h'
  exfalso
  aesop
  rename_i h_i
  simp [h_i]
  specialize ih (i+1) (source.set (Fin.mk i h_i) AssocList.nil) (List.foldl (fun d x => reinsertAux d x.1 x.2) target (AssocList.toList source[i]))
  simp at ih
  rw [ih]
  swap
  rw [← Nat.succ_eq_add_one, Nat.sub_succ, h]
  simp

  simp_rw [or_and_right, exists_or]
  constructor
  intro g
  cases g with
  | inl g =>
    rw [foldl_reinsertAux] at g
    cases g with
    | inl g =>
      left
      apply g
    | inr g =>
      right
      use source.get (Fin.mk i h_i)
      constructor
      use (Fin.mk i h_i)
      simp
      apply g
  | inr g =>
    rcases g with ⟨bkt,g,ab_mem⟩
    right
    use bkt
    rcases g with ⟨j, j_i, bkt_set⟩
    have j_isLt: j.val < Array.size source := by
      have h: j.val < Array.size (Array.set source {val:=i, isLt := h_i} AssocList.nil) := by
        apply j.isLt
      simp at h
      exact h

    have i_j: ¬ i = j.val := by
      by_contra p
      simp_rw [← p, ← Nat.succ_eq_add_one, Nat.succ_le_iff] at j_i
      simp at j_i
    constructor
    use Fin.mk j.val j_isLt
    simp
    constructor
    apply Nat.le_trans (m:= i+1)
    simp
    apply j_i
    simp [bkt_set]
    rw [Array.get_set_not_eq]
    simp
    aesop
    exact ab_mem

  intro g
  rw [foldl_reinsertAux]
  cases g with
  | inl g =>
    left
    left
    apply g
  | inr g =>
    rcases g with ⟨bkt, g, ab_mem⟩
    rcases g with ⟨j,i_j, bkt_j⟩
    by_cases j_i: i = j.val
    left
    right
    have source_eq: source[i] = source[j.val] := by
      simp_rw [j_i]
    rw [source_eq, ← bkt_j]
    apply ab_mem

    right
    use bkt
    have h_k: ∃ (k: Fin (Array.size (Array.set source { val := i, isLt := h_i } AssocList.nil))), k.val = j.val := by
      have k': j.val < (Array.size (Array.set source { val := i, isLt := h_i } AssocList.nil)) := by
        rw [Array.size_set]
        apply j.isLt
      use Fin.mk j.val k'
    rcases h_k with ⟨k, k_j⟩
    · constructor
      use k
      constructor
      · rw [k_j, ← Nat.succ_eq_add_one, Nat.succ_le_iff]
        apply Nat.lt_of_le_of_ne
        apply i_j
        exact j_i
      rw [Array.get_set]
      simp
      split
      · rename_i i_k
        rw [i_k] at j_i
        contradiction

      · rw [bkt_j]
        simp_rw [k_j]
        have h': source.size = Array.size (Array.set source { val := i, isLt := h_i } AssocList.nil) := by
          simp
        simp_rw [h']
        exact k.isLt
      exact ab_mem


lemma HashMap.Imp.expand_preserves_mem  (size : Nat) (buckets : Buckets A B) (a:A) (b:B): (∃ (bkt: AssocList A B),  bkt ∈ buckets.1 ∧ (a,b) ∈ bkt.toList) ↔ ∃ (bkt: AssocList A B),  bkt ∈ (expand size buckets).buckets.1 ∧  (a,b) ∈ bkt.toList := by
  unfold expand
  simp
  simp [HashMap.Imp.expand_go_mem]
  unfold Buckets.mk
  unfold mkArray


  constructor
  intro h
  rcases h with ⟨bkt, bkt_mem, ab_mem⟩
  use bkt
  constructor
  right
  rw [Array.mem_iff_exists] at bkt_mem
  apply bkt_mem
  apply ab_mem


  intro h
  rcases h with ⟨bkt, bkt_mem, ab_mem⟩
  use bkt
  constructor
  cases bkt_mem with
  | inl h =>
    unfold Buckets.mk at h
    simp at h
    rw [Array.mem_def] at h
    simp at h
    rw [List.mem_replicate] at h
    rcases h with ⟨_, empty⟩
    rw [empty] at ab_mem
    unfold AssocList.toList at ab_mem
    contradiction
  | inr h =>
    rw [Array.mem_iff_exists]
    apply h

  apply ab_mem

lemma HashMap.Imp.Buckets.distinct_elements (buckets: HashMap.Imp.Buckets A B) (wf: HashMap.Imp.Buckets.WF buckets) (l: AssocList A B) (mem: l ∈ buckets.1): List.Pairwise (fun x y => ¬x.1 = y.1) l.toList := by
  have dist: ∀ (bucket : Batteries.AssocList A B),
  bucket ∈ buckets.val.data →
    List.Pairwise (fun (a b : A × B) => ¬(a.fst == b.fst) = true) (Batteries.AssocList.toList bucket) := by
      apply wf.distinct
  simp at dist
  apply dist
  rw [← Array.mem_def]
  apply mem

lemma HashMap.Imp.Buckets.element_member_in_hash_bucket (a: A ) (b: B) (buckets: HashMap.Imp.Buckets A B) (wf: HashMap.Imp.Buckets.WF buckets) (i: Fin (buckets.1.size)): (a,b) ∈ buckets.1[↑i].toList →  i.val = USize.toNat (mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
  have hash_self: ∀ (i : Nat) (h : i < Array.size buckets.val),
  Batteries.AssocList.All (fun (k : A) (_ : B) => USize.toNat (UInt64.toUSize (hash k) % Array.size buckets.val) = i) buckets.val[i] := by
    apply wf.hash_self
  specialize hash_self i.val i.isLt
  unfold AssocList.All at hash_self
  simp at hash_self
  unfold mkIdx
  simp
  intro h
  apply Eq.symm
  apply hash_self
  apply h


lemma HashMap.Imp.insert_semantics (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (a a': A) (b b':B): (m.insert a b).kv_member a' b' ↔ (m.kv_member a' b' ∧ a ≠ a') ∨ (a, b) = (a', b') :=
by
  rw [← Imp.kv_member_iff_in_kv (wf:=wf), ← Imp.kv_member_iff_in_kv (wf:= Imp.WF.insert wf)]
  cases m with
  | mk size buckets =>
    rw [Batteries.HashMap.Imp.WF_iff] at wf
    simp at wf
    rcases wf with ⟨_, wf⟩
    unfold insert
    simp
    rw [cond_eq_if]
    unfold kv
    unfold Buckets.kv
    simp
    rw [Array.foldl_union, Array.foldl_union]
    simp

    split
    rename_i mem
    simp at mem
    simp
    rw [Buckets.mem_update]
    rw [splitArrayLemma (i:= USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a)))) (h:= (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)]
    simp
    simp_rw [cond_eq_if]
    rcases mem with ⟨b_,mem⟩
    rw [List.replaceF_distinct_mem]
    simp
    constructor
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        left
        rcases h with ⟨h, a_a'⟩
        constructor
        left
        apply h
        apply Ne.symm
        apply a_a'
      | inr h =>
        right
        simp [h]
    | inr h =>
      left
      constructor
      right
      apply h
      rcases h with ⟨j, j_hash, ab'_mem⟩
      by_contra a_a'
      have j_hash': j = USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
        apply HashMap.Imp.Buckets.element_member_in_hash_bucket
        apply wf
        rw [a_a']
        apply ab'_mem
      contradiction
    intro h
    cases h with
    | inl h =>
      rcases h with ⟨h, a_a'⟩
      cases h with
      | inl h =>
        left
        left
        constructor
        apply h
        apply Ne.symm
        apply a_a'
      | inr h =>
        right
        apply h
    | inr h =>
      left
      right
      simp [h]
    apply HashMap.Imp.Buckets.distinct_elements
    apply wf
    apply Array.get_mem (as:=buckets.1) (i:= Fin.mk (USize.toNat (mkIdx buckets.2 (UInt64.toUSize (hash a)))) (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)
    use (a,b_)



    rename_i a_mem
    simp at a_mem
    split
    simp
    rw [HashMap.Imp.Buckets.mem_update]
    simp
    rw [splitArrayLemma (i:= USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a)))) (h:= (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)]
    simp
    constructor
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        right
        simp [h]
      | inr h =>
        left;
        constructor
        left
        apply h
        by_contra p
        specialize a_mem b'
        rw [← p] at h
        contradiction
    | inr h =>
      left
      constructor
      right
      apply h
      by_contra a_a'
      rcases h with ⟨j, j_idx, ab'_mem⟩
      have j_idx': ↑j = USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
        apply  HashMap.Imp.Buckets.element_member_in_hash_bucket a b'
        apply wf
        rw [a_a']
        apply ab'_mem
      contradiction
    intro h
    cases h with
    | inl h =>
      rcases h with ⟨h, _⟩
      cases h with
      | inl h =>
        left;right;
        apply h
      | inr h =>
        right
        apply h
    | inr h =>
      left;left
      simp [h]


    rw [← HashMap.Imp.expand_preserves_mem]
    rw [HashMap.Imp.Buckets.mem_update]
    rw [splitArrayLemma (i:= USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a)))) (h:= (mkIdx buckets.2 (UInt64.toUSize (hash a))).2)]
    simp
    constructor
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        right
        simp [h]
      | inr h =>
        left
        constructor
        left
        apply h
        by_contra p
        specialize a_mem b'
        rw [p] at a_mem
        rw [p] at h
        contradiction
    | inr h =>
      left
      constructor
      right
      apply h
      by_contra p
      rcases h with ⟨j, j_mdIx, ab'_mem⟩
      rw [← p] at ab'_mem
      have j_idx': j = USize.toNat ↑(mkIdx buckets.2 (UInt64.toUSize (hash a))) := by
        apply HashMap.Imp.Buckets.element_member_in_hash_bucket a b'
        apply wf
        apply ab'_mem
      contradiction

    intro h
    cases h with
    | inl h =>
      rcases h with ⟨h,_⟩
      cases h with
      | inl h =>
        left
        right
        apply h
      | inr h =>
        right
        apply h
    | inr h =>
      left
      left
      simp [h]

lemma swap_not_equal (a a':A): ¬ a = a' ↔ ¬ a' = a :=
by
  aesop

lemma List.Pairwise_diff_to_element_if_all_diff (l: AssocList A B)(a:A) (h:List.Pairwise (fun x y => ¬x.1 = y.1) l.toList): List.Pairwise (fun x y => ¬((x.1 == a) = true ∧ (y.1 == a) = true)) (AssocList.toList l ) := by
  induction l with
  | nil =>
    simp
  | cons hda hdb tl ih =>
    simp
    constructor
    intro a' b' ab'_tl hda_a
    rw [← hda_a]
    simp at h
    rw [swap_not_equal]
    apply (And.left h)
    exact ab'_tl
    simp at ih
    apply ih
    simp at h
    apply And.right h

lemma Pairwise_diff_to_element_if_bucket (l: AssocList A B) (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (mem: l ∈ m.buckets.1) (a:A): List.Pairwise (fun x y => ¬((x.1 == a) = true ∧ (y.1 == a) = true))
  (AssocList.toList l ) := by
    have distinct: List.Pairwise (fun x y => ¬x.1 = y.1) l.toList := by
      apply HashMap.Imp.Buckets.distinct_elements
      rw [HashMap.Imp.WF_iff] at wf
      apply And.right wf
      exact mem
    simp at distinct
    apply List.Pairwise_diff_to_element_if_all_diff
    exact distinct

lemma HashMap.Imp.find_iff_kv (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (a:A) (b:B): m.find? a = some b ↔ m.kv_member a b = true := by
  cases m with
  | mk size buckets =>
    unfold kv_member
    unfold find?
    simp
    rw [AssocList.mem_containsKeyValue_iff_mem_toList (ab:=(a,b))]
    constructor
    intro h
    rcases h with ⟨a',mem⟩
    rw [List.find?_mem_iff] at mem
    simp at mem
    rcases mem with ⟨mem, a_a'⟩
    rw [a_a'] at mem
    exact mem
    apply Pairwise_diff_to_element_if_bucket
    use wf
    simp
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)

    intro h
    use a
    rw [List.find?_mem_iff]
    simp
    exact h
    apply Pairwise_diff_to_element_if_bucket
    use wf
    simp
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)



def HashMap.keys' (m: HashMap A B): Finset A := m.val.keys'

lemma HashMap.contains_iff (m: HashMap A B) (a: A): m.contains a ↔ a ∈ m.keys' :=
by
  unfold contains
  unfold keys'
  rw [Imp.contains_iff]
  apply m.2

def HashMap.kv_member (m: HashMap A B) (a: A) (b:B): Bool := m.1.kv_member a b

lemma HashMap.find_iff_kv (m: HashMap A B)  (a:A) (b:B): m.find? a = some b ↔ m.kv_member a b = true := by
  unfold find?
  unfold kv_member
  apply HashMap.Imp.find_iff_kv
  exact m.2

lemma HashMap.keys'_iff_kv (m: HashMap A B) (a:A): a ∈ m.keys' ↔ ∃ (b:B), m.kv_member a b:= by
  cases m with
  | mk m wf =>
    unfold keys'
    unfold kv_member
    simp
    rw [HashMap.Imp.keys'_iff_kv]
    simp_rw [HashMap.Imp.kv_member_iff_in_kv (wf:=wf)]


lemma HashMap.insert_semantics (m: HashMap A B) (a a': A) (b b':B): (m.insert a b).kv_member a' b' ↔ (m.kv_member a' b' ∧ a' ≠ a) ∨ (a, b) = (a', b') :=
by
  unfold kv_member
  unfold insert
  simp [HashMap.Imp.insert_semantics m.1 m.2 a a' b b']
  tauto

lemma HashMap.contains_insert (m : HashMap A B) (a a': A) (b:B): (m.insert a b).contains a' ↔ m.contains a' ∨ a == a' := by
  simp_rw [HashMap.contains_iff, HashMap.keys'_iff_kv]
  constructor
  intro h
  rcases h with ⟨b',h⟩
  rw [HashMap.insert_semantics] at h
  by_cases a_a': a = a'
  simp [a_a']

  simp [a_a'] at *
  use b'
  simp [h]

  intro h'
  by_cases a_a': a = a'
  use b
  rw [insert_semantics]
  right
  rw [a_a']

  simp[a_a'] at h'
  rcases h' with ⟨b', h⟩
  use b'
  rw [insert_semantics]
  left
  simp [h, a_a']
  aesop

lemma HashMap.Imp.contains_iff_find? (m: HashMap.Imp A B) (wf: HashMap.Imp.WF m) (a:A): m.contains a ↔ ∃ (b:B), m.find? a = some b := by
  unfold contains
  unfold find?
  cases m with
  | mk size buckets =>
    simp
    constructor
    intro h
    rcases h with ⟨b, mem⟩
    use b
    use a
    rw [List.find?_mem_iff]
    simp
    exact mem
    apply Pairwise_diff_to_element_if_bucket
    use wf
    simp
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)

    intro h
    rcases h with ⟨b,a',mem⟩
    use b
    rw [List.find?_mem_iff] at mem
    simp at mem
    aesop
    apply Pairwise_diff_to_element_if_bucket
    use wf
    simp
    exact Array.get_mem buckets.1 (Fin.mk (mkIdx buckets.2 (hash a).toUSize).1.toNat (mkIdx buckets.2 (hash a).toUSize).2)


lemma HashMap.find_insert (m: HashMap A B) (a a': A) (b :B): (m.insert a b).find? a' = if a' = a then some b else m.find? a' := by
  split
  rename_i h
  rw [find_iff_kv, insert_semantics, h]
  right
  rfl

  rename_i h
  cases h': find? m a' with
  | some b2 =>
    rw [find_iff_kv, insert_semantics]
    left
    constructor
    rw [← find_iff_kv]
    exact h'
    aesop
  | none =>
    rw [Option.eq_none_iff_forall_not_mem]
    by_contra p
    simp at p
    rcases p with ⟨b2, find_b2⟩
    rw [find_iff_kv, insert_semantics] at find_b2
    simp[h] at find_b2
    cases find_b2 with
    | inl h_1 =>
      rw [← find_iff_kv] at h_1
      rw [h_1] at h'
      simp at h'
    | inr h_1 =>
      aesop


lemma HashMap.contains_iff_find? (m: HashMap A B)  (a:A): m.contains a ↔ ∃ (b:B), m.find? a = some b := by
  unfold contains
  unfold find?
  apply HashMap.Imp.contains_iff_find?
  exact m.2

lemma HashMap.contains_of_find? (m: HashMap A B)  (a:A) (b:B) (h: m.find? a = some b): m.contains a := by
  rw [contains_iff_find?]
  use b

lemma HashMap.findD_eq_find? (m: HashMap A B) (a:A) (b:B): m.findD a b = match m.find? a with
                    | some b' => b'
                    | none => b := by
  unfold findD
  rw [Option.getD_eq_iff]
  aesop

lemma HashMap.not_contains_find_none (m: HashMap A B) (a:A) (h: ¬ m.contains a = true): m.find? a = none := by
  rw [contains_iff_find?] at h
  simp at h
  cases h':find? m a with
  | some b =>
    specialize h b
    contradiction
  | none =>
    rfl

-- Axioms for HashMap

theorem HashMap.findD_is_default_when_not_contains (hm : HashMap A B) (a : A) (h : ¬ hm.contains a) : ∀ b, hm.findD a b = b := by
  intro b
  rw [findD_eq_find?]
  split
  rename_i b' find
  have mem: contains hm a = true := by
    apply HashMap.contains_of_find?
    exact find
  contradiction

  rfl


def HashMap.Imp.Buckets.toList (buckets : Imp.Buckets A B) : List (A × B) := List.foldl (fun mb a => List.foldl (fun mb a => a :: mb) mb a.toList) [] buckets.val.data

-- TODO: probably remove if indeed not required
-- def HashMap.Imp.Buckets.get_for_key (buckets : Imp.Buckets A B) (a : A) : AssocList A B := 
--   let index := (mkIdx buckets.prop (hash a).toUSize)
--   buckets.val[index.val.toNat]

theorem HashMap.Imp.Buckets.in_toList_means_in_list_at_index (buckets : Imp.Buckets A B) (wf : buckets.WF) : (a, b) ∈ buckets.toList -> a ∈ buckets.keys' := by 
  intro h
  unfold keys'
  simp [Array.foldl_eq_foldl_data]
  sorry

theorem HashMap.Imp.Buckets.in_list_at_index_means_in_toList (buckets : Imp.Buckets A B) : a ∈ buckets.keys' -> ∃ b, (a,b) ∈ buckets.toList := by 
  intro h
  rw [keys'_iff_kv] at h
  cases h with | intro b hb =>
    unfold kv at hb
    simp [Array.foldl_eq_foldl_data] at hb
    exists b
    unfold toList
    revert hb
    have : ∀ bucket_list : List _, (a, b) ∈ List.foldl (fun x y => x ∪ y.toList.toFinset) bucket_list.toFinset buckets.val.data -> (a, b) ∈ List.foldl (fun mb a => List.foldl (fun mb a => a :: mb) mb a.toList) (List.foldl (fun mb a => a :: mb) [] bucket_list) buckets.val.data := by 
      induction buckets.val.data with 
      | nil => 
        intro bucket_list 
        induction bucket_list with 
        | nil => simp
        | cons head tail ih_inner => 
          intro h
          simp at h 
          simp
          cases h with 
          | inl hl => rw [hl]; sorry
          | inr hr => simp at ih_inner; have applied_ih_inner := ih_inner hr; sorry
      | cons bucket buckets ih => 
        intro bucket_list hb
        simp at hb
        simp
        sorry
    apply this []

theorem HashMap.in_projection_of_toList_iff_contains (hm : HashMap A B) (a : A) : a ∈ hm.toList.map Prod.fst ↔ hm.contains a := by
  rw [List.mem_map]
  simp
  unfold toList
  unfold fold
  unfold Imp.fold
  unfold Id.run
  unfold Imp.foldM
  simp [Array.foldlM_eq_foldlM_data, List.foldlM_eq_foldl]
  
  rw [contains_iff] 
  
  constructor
  . intro h 
    cases h with | intro b hb => 
      have wf : hm.val.buckets.WF := (Imp.WF.out hm.prop).2
      apply Imp.Buckets.in_toList_means_in_list_at_index _ wf
      apply hb
  . intro h 
    unfold keys' at h
    unfold Imp.keys' at h
    simp at h
    cases Imp.Buckets.in_list_at_index_means_in_toList _ h with | intro b hb => exists b

theorem HashMap.ofList_mapped_to_pair_contains_iff_list_elem (l : List A) (a : A) : ∀ b : B, (Batteries.HashMap.ofList (l.map (fun a => (a, b)))).contains a ↔ a ∈ l := by sorry

theorem HashMap.for_keys_in_map_inserting_findD_does_not_change (hm : HashMap A B) (a : A) (a_in_hm : hm.contains a) : ∀ b, hm.insert a (hm.findD a b) = hm := by sorry

theorem HashMap.findD_ofList_is_list_find_getD (l : List (A × B)) (a : A) : ∀ b, (Batteries.HashMap.ofList l).findD a b = ((l.find? (fun x => x.fst == a)).map Prod.snd).getD b := by sorry

theorem HashMap.findD_insert (hm : HashMap A B) (a a' : A) (h: ¬ hm.contains a = true): ∀ b, (hm.insert a b).findD a' b = hm.findD a' b := by
  intro b
  rw [findD_eq_find?, findD_eq_find?, find_insert]
  by_cases a_a': a' = a
  simp [a_a']
  have find_hm : find? hm a = none := by
    apply not_contains_find_none
    exact h
  simp [find_hm]

  simp [a_a']

theorem HashMap.findD_insert' (hm : HashMap A B) (a : A) (b : B) : ∀ b', (hm.insert a b).findD a b' = b := by
  intro b'
  rw [findD_eq_find?, find_insert]
  simp

theorem HashMap.findD_insert'' (hm : HashMap A B) (a a' : A) (h : a ≠ a') : ∀ b b', (hm.insert a b).findD a' b' = hm.findD a' b' := by
  intro b b'
  rw [findD_eq_find?, findD_eq_find?, find_insert]
  aesop

end HashMap

abbrev HashSet (A:Type) [Hashable A] [DecidableEq A] := HashMap A Unit

section HashSet
variable {A:Type} [Hashable A] [DecidableEq A][LawfulBEq A]

def HashSet.empty: HashSet A := HashMap.empty

def HashSet.contains (S: HashSet A) (a:A): Bool := HashMap.contains S a

def HashSet.insert (S: HashSet A) (a:A): HashSet A := HashMap.insert S a ()

lemma HashSet.contains_insert {S: HashSet A} (a:A ): ∀ (a':A), (S.insert a).contains a' ↔ S.contains a' ∨ a = a' := by
  intro a'
  unfold insert
  unfold contains
  simp [HashMap.contains_iff, HashMap.keys'_iff_kv]
  constructor
  intro h
  rcases h with ⟨b, h⟩
  rw [HashMap.insert_semantics] at h
  simp at h
  cases h with
  | inl h =>
    left
    use b
    simp[h]
  | inr h =>
    right
    apply h

  intro h
  use ()
  rw [HashMap.insert_semantics]
  simp
  by_cases a_a': a = a'
  simp [a_a']

  simp [a_a']
  simp [a_a'] at h
  constructor
  rcases h with ⟨_, h⟩
  apply h
  apply Ne.symm
  apply a_a'


lemma HashSet.empty_contains: ∀ (a:A), ¬ HashSet.empty.contains a :=
by
  intro a
  unfold contains
  unfold empty
  unfold HashMap.empty
  unfold mkHashMap
  unfold HashMap.Imp.empty
  unfold HashMap.contains
  simp
  unfold HashMap.Imp.empty'
  unfold HashMap.Imp.contains
  simp
  unfold HashMap.Imp.Buckets.mk
  simp

  def HashSet.Subset (S S': HashSet A): Prop := ∀ (b:A), S.contains b → S'.contains b

instance : HasSubset (HashSet A) := ⟨HashSet.Subset⟩

lemma HashSet.Subset.refl {S: HashSet A} : S ⊆ S :=
by
  unfold_projs at *
  unfold Subset at *
  simp


lemma HashSet.Subset.trans {S1 S2 S3: HashSet A} (h1: S1 ⊆ S2) (h2: S2 ⊆ S3): S1 ⊆ S3 :=
by
  unfold_projs at *
  unfold Subset at *
  intro b S1_b
  apply h2
  apply h1
  apply S1_b

lemma HashSet.Subset.Iff  {S1 S2: HashSet A} : S1 ⊆ S2 ↔ (∀ (a:A), S1.contains a → S2.contains a) :=
by
  unfold_projs
  unfold HashSet.Subset
  simp


end HashSet
