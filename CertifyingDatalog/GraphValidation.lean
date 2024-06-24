import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation
import CertifyingDatalog.HashSets
import Mathlib.Data.List.Card
import Mathlib.Data.Finset.Card

abbrev PreGraph (A: Type) [DecidableEq A] := Array (A × List ℕ)

def Array.enum {A: Type} (as: Array A): Array (ℕ × A) := {data:= List.enum as.data}

lemma Array.enum_mem (as: Array A) (n:ℕ): n ∈ Array.map Prod.fst as.enum ↔ n < as.size := by
  rw [Array.mem_def,Array.map_data, enum]
  simp

namespace PreGraph
  variable {A: Type}[DecidableEq A]

  def vertices (pg: PreGraph A): List ℕ := (Array.map Prod.fst ( Array.enum pg)).toList

  def labels (pg: PreGraph A): List A := (Array.map Prod.fst pg).toList

  lemma inVerticesIffLessThanLength (n: ℕ) (pg: PreGraph A): n ∈ pg.vertices ↔ n < pg.size := by
    unfold vertices
    unfold Array.enum
    simp

  def label (pg: PreGraph A) (n: ℕ) (mem: n ∈ pg.vertices): A := Prod.fst (Array.get pg (Fin.mk n (Iff.mp (inVerticesIffLessThanLength n pg) mem)))

  def successors (pg: PreGraph A) (n:ℕ): List ℕ := Array.getD (Array.map Prod.snd pg) n []

  def complete (pg: PreGraph A):= ∀ (n m: ℕ), n ∈ pg.vertices → m ∈ pg.successors n → m ∈ pg.vertices

  def successorLabels (pg: PreGraph A) (n: ℕ) (mem: n ∈ pg.vertices) (compl: pg.complete): List A := List.map (fun ⟨x, _h⟩ => label pg x (compl n x mem _h)) (pg.successors n).attach

  end PreGraph

abbrev Graph (A: Type) [DecidableEq A] [Hashable A] := { pg : PreGraph A // pg.complete }

namespace Graph
  variable {A: Type}[DecidableEq A][Hashable A]

  def vertices (g : Graph A) : List ℕ := g.val.vertices
  def successors (g : Graph A) (n : ℕ) : List ℕ := g.val.successors n

  def label (g: Graph A) (n: ℕ) (mem: n ∈ g.vertices):A := g.val.label n mem

  def successorLabels (g: Graph A) (n: ℕ) (mem: n ∈ g.vertices): List A := g.val.successorLabels n mem g.2

  def labels (g: Graph A): List A := g.val.labels

  theorem complete (g : Graph A) : ∀ (n: ℕ ), n ∈ g.vertices →  ∀ (m: ℕ), m ∈ g.successors n → m ∈ g.vertices := by
    aesop
end Graph

section dfs
variable {A: Type}[DecidableEq A][Hashable A] {B: Type} [DecidableEq B] [Hashable B] [DecidableEq B]
open Std

lemma pred_lt (n m: ℕ) (h:n < m ): n.pred < m :=
by
  cases n with
  | zero =>
    unfold Nat.pred
    simp
    apply h
  | succ n =>
    unfold Nat.pred
    simp
    apply Nat.lt_of_succ_lt h

lemma Nat.pred_gt_zero_iff (n: ℕ): n.pred > 0 ↔ n ≥ 2 :=
by
  cases n with
  | zero =>
    simp
  | succ n =>
    cases n with
    | zero =>
      simp
    | succ m =>
      simp
      rw [Nat.two_le_iff]
      simp


def isWalk (l: List ℕ) (G: Graph A): Prop :=
 ( ∀ (a:ℕ ), a ∈ l → a ∈ G.vertices ) ∧ ∀ (i: ℕ), i > 0 → ∀ (g: i < l.length), l.get (Fin.mk i.pred (pred_lt i l.length g)) ∈ G.successors (l.get (Fin.mk i g) )

 lemma isWalkSingleton (G: Graph A) (a:ℕ) (mem: a ∈ G.vertices): isWalk [a] G :=
by
  unfold isWalk
  constructor
  simp
  apply mem

  simp
  intro i i_gt_0 i_0
  simp [i_0] at i_gt_0


lemma ge_two_im_gt_zero (n: ℕ) (h: n ≥ 2): n > 0 :=
by
  cases n with
  | zero =>
    simp at h
  | succ m =>
    simp

def isCycle (l: List ℕ) (G: Graph A): Prop :=
  if h: l.length < 2
  then False
  else
    have l_not_zero: 0 < l.length :=
    by
      cases ll: l.length with
      | zero =>
        rw [ll] at h
        simp at h
      | succ n =>
        simp


  isWalk l G ∧ l.get (Fin.mk 0 l_not_zero) = l.get (Fin.mk l.length.pred (Nat.pred_lt (Ne.symm (Nat.ne_of_lt l_not_zero))))

lemma IsWalkOfisCycle (l: List ℕ) (G: Graph A) (h: isCycle l G): isWalk l G :=
by
  unfold isCycle at h
  by_cases h' : List.length l < 2
  simp [h'] at h

  simp [h'] at h
  simp [h]

def isAcyclic (G: Graph A) := ∀ (l: List ℕ), ¬ isCycle l G





lemma isWalk_extends_successors {a: ℕ} {l: List ℕ} {G: Graph A} (walk: isWalk (a::l) G): ∀ (b:ℕ), b ∈ (G.successors a) → isWalk (b::a::l) G :=
by
  intro b b_mem
  unfold isWalk
  unfold isWalk at walk
  rcases walk with ⟨subs,connected⟩
  constructor
  intro a'
  simp

  intro h
  cases h with
  | inl h =>
    rw [h]
    apply G.complete a
    apply subs
    simp
    apply b_mem
  | inr h =>
    apply subs
    simp
    apply h

  intro i i_zero i_len
  cases i with
  | zero =>
    simp at i_zero
  | succ j =>
    rw [List.get_cons_succ]
    cases j with
    | zero =>
      simp
      apply b_mem
    | succ k =>
      simp
      specialize connected (Nat.succ k)
      simp at connected
      simp at i_len
      have g: Nat.succ k < List.length (a :: l) := by
        rw [Nat.succ_lt_succ_iff] at i_len
        simp
        rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
        apply i_len
      specialize connected g
      apply connected

lemma isWalkImplSubset {l: List ℕ} {G: Graph A} (walk: isWalk l G ): l.toFinset ⊆ G.vertices.toFinset :=
by
  rw [Finset.subset_iff]
  unfold isWalk at walk
  rcases walk with ⟨h,_⟩
  simp [List.mem_toFinset]
  apply h

lemma isWalkImplSubset' {l: List ℕ} {G: Graph A} (walk: isWalk l G ): ∀ (a:ℕ), a ∈ l → a ∈ G.vertices :=
by
  unfold isWalk at walk
  rcases walk with ⟨walk,_⟩
  apply walk

lemma isWalk_of_cons {a: ℕ} {l:List ℕ} {G:Graph A} (walk: isWalk (a::l) G): isWalk l G :=
by
  unfold isWalk at *
  rcases walk with ⟨subs, conn⟩
  constructor
  intro a' a'_l
  apply subs
  simp
  right
  apply a'_l

  intro i i_zero i_len
  specialize conn (Nat.succ i)
  simp at conn
  have g:  Nat.succ i < List.length (a :: l) := by
    simp
    apply Nat.succ_lt_succ
    apply i_len
  specialize conn g
  cases i with
  | zero =>
    simp at i_zero
  | succ j =>
    rw [List.get_cons_succ] at conn
    apply conn

lemma getFirstForNonequal_isLt  (l: List A) (h:l ≠ []): 0 < l.length :=
by
  cases l with
  | nil => simp at h
  | cons hd tl => simp

lemma getLastForNonequal_isLt (l: List A) (h:l ≠ []): l.length.pred < l.length :=
by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    apply Nat.pred_lt
    simp

def canReach (a b: ℕ) (G: Graph A):= ∃ (p: List ℕ) (neq: p ≠ []), isWalk p G ∧ p.get (Fin.mk 0 (getFirstForNonequal_isLt p neq)) = b ∧ p.get (Fin.mk p.length.pred (getLastForNonequal_isLt p neq)) = a

lemma canReach_refl (a:ℕ) (G: Graph A) (mem: a ∈ G.vertices): canReach a a G :=
by
  unfold canReach
  use [a]
  have neq: [a] ≠ [] := by
    simp
  use neq
  constructor
  unfold isWalk
  constructor
  intro a'
  simp
  intro h
  rw [h]
  apply mem

  intro i i_zero i_lt
  simp at i_lt
  rw [i_lt] at i_zero
  simp at i_zero
  simp


lemma canReachMem {a b: ℕ} {G: Graph A} (reach: canReach a b G): b ∈ G.vertices := by
  unfold canReach at reach
  rcases reach with ⟨p, _, walk, get_b, _⟩
  unfold isWalk at walk
  rcases walk with ⟨walk, _⟩
  apply walk
  rw [← get_b]
  apply List.get_mem



noncomputable def globalSuccessors (a:ℕ) (G: Graph A): Finset ℕ := Finset.filter_nc (fun b => canReach a b G) G.vertices.toFinset


lemma isWalkExtendBack (p: List ℕ) (a: ℕ) (G: Graph A) (walk: isWalk p G) (nonempty_p: p ≠ []) (mem: a ∈ G.vertices) (backExtend: p.get (Fin.mk p.length.pred (getLastForNonequal_isLt p nonempty_p)) ∈ G.successors a): isWalk (p++[a]) G :=
by
  unfold isWalk at *
  simp at *
  rcases walk with ⟨subs, conn⟩
  constructor
  intro b b_mem
  cases b_mem with
  | inl b_p =>
    apply subs b b_p
  | inr b_a =>
    rw [b_a]
    apply mem

  intro i i_zero i_len
  by_cases i_original: i < p.length
  rw [List.get_append i i_original]
  have i_original_pred: i.pred < p.length := by
    apply Nat.lt_trans (m:= i)
    apply Nat.pred_lt
    apply Ne.symm
    apply Nat.ne_of_lt
    apply i_zero
    apply i_original
  rw [List.get_append i.pred i_original_pred]
  apply conn i i_zero

  simp at i_original
  cases i_original with
  | refl =>
    rw [List.get_append_right (i:= p.length), List.get_append p.length.pred (getLastForNonequal_isLt p nonempty_p)]
    simp
    apply backExtend
    simp
    push_neg
    apply Nat.le_refl
  | step h =>
    rw [← Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at i_len
    simp at h
    rw [← not_lt] at h
    exact absurd i_len h

lemma globalSuccessorsSubsetWhenSuccessor (a b:ℕ) (G: Graph A) (mem: a ∈ G.vertices) (succ: b ∈ G.successors a): globalSuccessors b G ⊆ globalSuccessors a G:=
by
  rw [Finset.subset_iff]
  intro x
  rw [globalSuccessors, Finset.mem_filter_nc]
  intro h
  rcases h with ⟨reach, mem'⟩
  rw [globalSuccessors, Finset.mem_filter_nc]
  constructor
  unfold canReach at *
  rcases reach with ⟨p, neq, walk, get_x, get_b⟩
  use (p++[a])
  have neq': (p++[a]) ≠ [] := by
    simp
  use neq'
  constructor
  apply isWalkExtendBack p a G walk neq mem
  rw [get_b]
  apply succ

  constructor
  rw [List.get_append_left]
  apply get_x
  rw [List.get_append_right]
  simp
  simp
  simp
  apply mem'




lemma nodeNotInGlobalSuccessorOfSuccessorInAcyclic (a b:ℕ) (G: Graph A) (acyclic: isAcyclic G) (succ: b ∈ G.successors a): ¬  a ∈ globalSuccessors b G :=
by
  by_contra p
  unfold globalSuccessors at p
  rw [Finset.mem_filter_nc] at p
  rcases p with ⟨reach,mem⟩
  unfold canReach at reach
  rcases reach with ⟨p,nonempty, walk, get_a, get_b⟩
  have cycle: isCycle (p++[a]) G := by
    unfold isCycle
    simp
    cases p with
    | nil =>
      simp at nonempty
    | cons hd tl =>
      have h : ¬  List.length (hd :: tl) + 1 < 2 := by
        simp
        rw [← Nat.succ_eq_add_one]
        simp_arith
      simp only [h]
      simp
      constructor
      rw [← List.cons_append]
      apply isWalkExtendBack
      apply walk
      rw [← List.mem_toFinset]
      apply mem
      rw [get_b]
      apply succ
      simp

      rw [List.get_append_right]
      simp
      rw [List.get_eq_iff, List.get?_cons_zero, Option.some_inj] at get_a
      apply get_a
      simp
      simp


  unfold isAcyclic at acyclic
  specialize acyclic (p++[a])
  exact absurd cycle acyclic

lemma globalSuccessorsSSubsetWhenAcyclicAndSuccessor (G: Graph A) (a b: ℕ) (acyclic: isAcyclic G) (succ: b ∈ G.successors a) (mem_a: a ∈ G.vertices): globalSuccessors b G  ⊂ globalSuccessors a G :=
by
  rw [Finset.ssubset_def]
  constructor
  apply globalSuccessorsSubsetWhenSuccessor a b G mem_a succ

  rw [Finset.subset_iff]
  simp
  use a
  constructor
  unfold globalSuccessors
  rw [Finset.mem_filter_nc]
  constructor
  unfold canReach
  use [a]
  have neq: [a] ≠ [] := by
    simp
  use neq
  constructor
  apply isWalkSingleton
  apply mem_a
  constructor
  simp
  simp
  rw [List.mem_toFinset]
  apply mem_a

  apply nodeNotInGlobalSuccessorOfSuccessorInAcyclic
  apply acyclic
  apply succ





lemma removeFrontOfLtMin (a b c: ℕ) (hab: b ≤ a) (hac: c ≤ a) : a - b < a -c ↔ b > c :=
by
  induction a with
  | zero =>
    simp at *
    rw [hab, hac]
  | succ n ih =>
    cases hab with
    | refl =>
      cases hac with
      | refl =>
        simp
      | step hc =>
        simp
    | step hb =>
      cases hac with
      | refl =>
        simp
        apply Nat.le_succ_of_le hb
      | step hc =>
        specialize ih hb hc
        rw [← ih]
        rw [Nat.succ_sub hb, Nat.succ_sub hc]
        rw [Nat.succ_lt_succ_iff]


def getSubListToMember (l: List A) (a: A) (mem: a ∈ l): List A :=
  match l with
  | [] =>
    have h: False :=
    by
      simp at mem

    False.elim h
  | hd::tl =>
    if p: a = hd
    then [hd]
    else
      have mem': a ∈ tl :=
      by
        simp[p] at mem
        apply mem
      hd::getSubListToMember tl a mem'

lemma getSubListToMemberPreservesFront (hd a hd': A) (tl tl': List A) (mem: a ∈ hd'::tl') (result: getSubListToMember (hd'::tl') a mem = hd::tl): hd' = hd :=
by
  unfold getSubListToMember at result
  by_cases a_hd: a = hd'
  all_goals{
  simp [a_hd] at result
  simp [result]
  }

lemma zero_lt_inhabited_list_length (a:A) (l: List A) (mem: a ∈ l): 0 < l.length :=
by
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp



lemma getSubListToMemberNonEmpty (a: A) (l: List A) (mem: a ∈ l): getSubListToMember l a mem ≠ [] :=
by
  unfold getSubListToMember
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp
    by_cases a_hd: a = hd
    simp [a_hd]
    simp [a_hd]

lemma getSubListToMemberHasNotLengthZero (a: A) (l: List A) (mem: a ∈ l): List.length (getSubListToMember l a mem) ≠ 0 :=
by
  cases h:(getSubListToMember l a mem) with
    | nil =>
      have not_h: ¬  (getSubListToMember l a mem) = [] := by
        push_neg
        apply getSubListToMemberNonEmpty
      exact absurd h not_h
    | cons hd tl =>
      simp

lemma getSubListToMember_length (a: A) (l: List A) (mem: a ∈ l): List.length (getSubListToMember l a mem) = Nat.succ (Nat.pred (List.length (getSubListToMember l a mem))) :=
by
  apply Eq.symm
  apply Nat.succ_pred
  apply getSubListToMemberHasNotLengthZero


lemma getSubListToMember_len_le_original (a: A) (l: List A) (mem: a ∈ l): (getSubListToMember l a mem).length ≤ l.length :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    rw [Nat.one_eq_succ_zero, Nat.succ_le_succ_iff]
    apply Nat.zero_le

    simp [a_hd]
    simp[a_hd] at mem
    rw [Nat.succ_le_succ_iff]
    apply ih

lemma zero_lt_inhabited_list_length' (l: List A) (nonempty: l ≠ []): 0 < l.length :=
by
  cases l with
  | nil =>
    simp at nonempty
  | cons hd tl =>
    simp

lemma getSubListToMemberPreservesFront' (a:A) (l: List A) (mem: a ∈ l) : List.get l (Fin.mk 0 (zero_lt_inhabited_list_length a l mem)) = List.get (getSubListToMember l a mem) (Fin.mk 0 (zero_lt_inhabited_list_length' (getSubListToMember l a mem) (getSubListToMemberNonEmpty a l mem))) :=
by
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp
    apply Eq.symm
    rw [List.get_eq_iff]
    simp
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    simp [a_hd]


lemma getSubListToMemberEndsWithElement (a: A) (l: List A) (mem: a ∈ l): List.get? (getSubListToMember l a mem) (getSubListToMember l a mem).length.pred  = a  :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    simp [getSubListToMember]
    by_cases a_hd: a = hd
    subst a_hd
    simp

    simp [a_hd]
    simp[a_hd] at mem
    specialize ih mem

    rw [getSubListToMember_length, List.get?_cons_succ]
    apply ih




lemma getSubListToMemberPreservesWalk (l: List ℕ) (a:ℕ) (mem: a ∈ l) (G: Graph A) (walk: isWalk l G): isWalk (getSubListToMember l a mem) G :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    apply isWalkSingleton
    unfold isWalk at walk
    simp [walk]

    simp [a_hd]
    simp [a_hd] at mem
    specialize ih mem (isWalk_of_cons walk)
    unfold isWalk at *
    rcases walk with ⟨subs_ht, conn_ht⟩
    rcases ih with ⟨subs_ih, conn_ih⟩
    constructor
    intro b b_mem
    simp at b_mem
    cases b_mem with
    | inl b_hd =>
      apply subs_ht
      rw [b_hd]
      simp
    | inr b_tl =>
      apply subs_ih
      apply b_tl

    intro i i_zero i_len
    cases i with
    | zero =>
      simp at i_zero
    | succ j =>
      simp
      cases j with
      | zero =>
        simp
        specialize conn_ht (Nat.succ 0)
        simp at conn_ht
        simp at i_len
        have g: Nat.succ 0 < List.length (hd :: tl) := by
          simp
          apply Nat.lt_of_lt_of_le
          apply i_len
          apply Nat.succ_le_succ
          apply getSubListToMember_len_le_original

        specialize conn_ht g
        cases tl with
        | nil =>
          simp at mem
        | cons hd' tl' =>
          simp at conn_ht
          have isLt: Nat.zero < List.length (getSubListToMember (hd' :: tl') a mem) := by
            rw [getSubListToMember_length]
            apply Nat.zero_lt_succ
          have get_result: List.get (getSubListToMember (hd' :: tl') a mem) { val := 0, isLt := isLt } = hd' := by
            rw [List.get_eq_iff]
            simp
            unfold getSubListToMember
            by_cases a_hd: a = hd'
            simp [a_hd]

            simp [a_hd]
          simp [get_result]
          apply conn_ht
      | succ k =>
        specialize conn_ih (Nat.succ k)
        simp at conn_ih
        simp at i_len
        rw [Nat.succ_lt_succ_iff, ← Nat.succ_eq_add_one] at i_len
        specialize conn_ih i_len
        apply conn_ih

def reachesCycle (a:ℕ) (G: Graph A):= ∃ (c: List ℕ), isCycle c G ∧ ∃ (b: ℕ), b ∈ c ∧ canReach a b G

lemma NotreachesCycleIffSuccessorsNotReachCycle (a: ℕ) (G: Graph A) (mem: a ∈ G.vertices): ¬ reachesCycle a G ↔ ∀ (b:ℕ), b ∈ G.successors a → ¬ reachesCycle b G :=
by
  constructor
  intro h
  unfold reachesCycle at h
  simp at h
  by_contra p
  simp at p
  rcases p with ⟨x, x_succ, reach⟩
  unfold reachesCycle at reach
  rcases reach with ⟨c, cycle, b, b_c, reach_b_x⟩
  specialize h c cycle b b_c
  have reach_b_a: canReach a b G := by
    unfold canReach
    unfold canReach at reach_b_x
    rcases reach_b_x with ⟨p, neq, walk, get_b, get_x⟩
    use p++[a]
    have neq': p++[a] ≠ [] := by
      simp
    use neq'
    constructor
    apply isWalkExtendBack p a G walk neq mem
    rw [get_x]
    apply x_succ
    constructor
    rw [List.get_append_left]
    apply get_b
    rw [List.get_append_right]
    simp
    simp
    simp
  exact absurd reach_b_a h

  --back direction
  intro h
  by_contra p
  unfold reachesCycle at p
  rcases p with ⟨c, cycle, b, b_c, reach_b_a⟩
  unfold canReach at reach_b_a
  rcases reach_b_a with ⟨p, neq, walk, get_b, get_a⟩
  by_cases b_succ: b ∈ G.successors a
  have reachCirc_b: reachesCycle b G := by
    unfold reachesCycle
    use c
    constructor
    apply cycle
    use b
    constructor
    apply b_c
    unfold canReach
    use [b]
    have neq': [b] ≠ [] := by
      simp
    use neq'
    constructor
    apply isWalkSingleton
    apply G.complete
    apply mem
    apply b_succ
    simp

  specialize h b b_succ
  exact absurd reachCirc_b h

  -- b not connected with a directly
  by_cases singletonWalk: p.length = 1
  have a_b: a = b := by
    simp [singletonWalk] at get_a
    rw [← get_a, get_b]

  have succ_in_c: ∃ (d:ℕ), d ∈ c ∧ d ∈ G.successors a := by
    unfold isCycle at cycle
    by_cases h : List.length c < 2
    simp [h] at cycle
    simp [h] at cycle
    rcases cycle with ⟨walk, ends⟩
    unfold isWalk at walk
    rcases walk with ⟨subs,conn⟩
    have isLt_zero_c: 0 < c.length := by
      cases c with
      | nil =>
        simp at b_c
      | cons hd tl =>
        simp
    rw [List.mem_iff_get?] at b_c
    rcases b_c with ⟨n, get_c_b⟩
    cases n with
    | zero =>
      specialize conn (Nat.pred c.length)
      have conn_1: Nat.pred (List.length c) > 0 := by
        simp at h
        cases c with
        | nil =>
          simp at h
        | cons hd tl =>
          cases tl with
          | nil =>
            simp at h
          | cons hd tl =>
            simp
      specialize conn conn_1
      have g : Nat.pred (List.length c) < List.length c := by
        apply Nat.pred_lt
        cases c with
        | nil =>
          simp at h
        | cons hd tl =>
          simp
      specialize conn g
      have ha: List.get c (Fin.mk (Nat.pred (List.length c)) g) = b := by
        rw [← ends, List.get_eq_iff]
        simp
        apply get_c_b
      rw [ha, ← a_b] at conn
      have isLt': Nat.pred (Nat.pred (List.length c)) < c.length := by
        apply Nat.lt_of_le_of_lt (m:= Nat.pred c.length)
        rw [Nat.pred_le_iff, Nat.succ_pred]
        apply Nat.pred_le
        cases c with
        | nil =>
          simp at h
        | cons hd tl =>
          simp
        apply Nat.pred_lt
        cases c with
        | nil =>
          simp at h
        | cons hd tl =>
          simp
      use (List.get c (Fin.mk (Nat.pred (Nat.pred (List.length c))) isLt' ))
      constructor
      apply List.get_mem
      apply conn
    | succ m =>
      specialize conn (Nat.succ m)
      have conn1: Nat.succ m > 0 := by
        simp
      specialize conn conn1
      rw [List.get?_eq_some] at get_c_b
      rcases get_c_b with ⟨g,c_get⟩
      specialize conn g
      have isLt: Nat.pred (Nat.succ m) < c.length := by
        simp
        apply Nat.lt_trans (m:= Nat.succ m)
        apply Nat.lt_succ_self
        apply g
      use List.get c (Fin.mk (Nat.pred (Nat.succ m)) isLt)
      constructor
      apply List.get_mem
      rw [c_get, ← a_b] at conn
      apply conn


  rcases succ_in_c with ⟨d, d_c, d_succ⟩
  specialize h d d_succ
  have reachCirc_d: reachesCycle d G := by
    unfold reachesCycle
    use c
    constructor
    apply cycle
    use d
    constructor
    apply d_c
    unfold canReach
    use [d]
    have neq': [d] ≠ [] := by
      simp
    use neq'
    simp
    apply isWalkSingleton
    apply isWalkImplSubset' (IsWalkOfisCycle c G cycle) d d_c
  exact absurd reachCirc_d h


  have isLt: Nat.pred (Nat.pred p.length) < p.length := by
    cases p with
    | nil =>
      simp at neq
    | cons hd tl =>
      cases tl with
      | nil =>
        simp
      | cons hd' tl' =>
        simp
        apply Nat.lt_trans (m:= Nat.succ tl'.length)
        apply Nat.lt_succ_self
        apply Nat.lt_succ_self

  have reachCirc: reachesCycle (p.get (Fin.mk (Nat.pred (Nat.pred p.length)) isLt)) G := by
    unfold reachesCycle
    use c
    constructor
    apply cycle
    use b
    constructor
    apply b_c
    unfold canReach
    have mem_p: (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) ∈ p := by
      apply List.get_mem

    use (getSubListToMember p (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) mem_p)
    have neq': (getSubListToMember p (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) mem_p) ≠ [] := by
      apply getSubListToMemberNonEmpty
    use neq'
    constructor
    apply getSubListToMemberPreservesWalk (walk:= walk)
    constructor
    rw [← get_b]
    apply Eq.symm
    apply getSubListToMemberPreservesFront'
    rw [List.get_eq_iff]
    simp
    apply getSubListToMemberEndsWithElement


  specialize h (List.get p { val := Nat.pred (Nat.pred (List.length p)), isLt := isLt })
  unfold isWalk at walk
  rcases walk with ⟨_, conn⟩
  specialize conn  (Nat.pred (List.length p))

  have gt_zero:  Nat.pred (List.length p) > 0 := by
    cases p with
    | nil =>
      simp at neq
    | cons hd tl =>
      simp
      cases tl with
      | nil =>
        simp at singletonWalk
      | cons hd' tl' =>
        simp

  have g : Nat.pred (List.length p) < List.length p := by
    cases p with
    | nil =>
      simp at neq
    | cons hd tl =>
      simp
  specialize conn gt_zero g
  rw [get_a] at conn
  specialize h conn
  exact absurd reachCirc h

lemma acyclicIffAllNotReachCycle (G: Graph A): isAcyclic G ↔ ∀ (a:ℕ), a ∈ G.vertices → ¬ reachesCycle a G :=
by
  constructor
  intro acyclic
  intro a
  unfold reachesCycle
  simp
  intro _ c cycle
  unfold isAcyclic at acyclic
  specialize acyclic c
  exact absurd cycle acyclic

  intro h
  by_contra cyclic
  unfold isAcyclic at cyclic
  simp at cyclic
  rcases cyclic with ⟨c, cycle⟩
  unfold isCycle at cycle
  by_cases g:List.length c < 2
  simp [g] at cycle
  simp [g] at cycle
  have isLt: 0 < List.length c := by
    cases c with
    | nil =>
      simp at g
    | cons hd tl =>
      simp
  specialize h (List.get c (Fin.mk 0 isLt))
  unfold reachesCycle at h
  simp at h

  have get_c_mem: List.get c { val := 0, isLt := isLt } ∈ G.vertices := by
    apply isWalkImplSubset'
    rcases cycle with ⟨walk, _⟩
    apply walk
    apply List.get_mem

  specialize h get_c_mem c
  unfold isCycle at h
  simp [g, cycle] at h
  specialize h (List.get c (Fin.mk 0 isLt))
  simp [List.get_mem] at h
  unfold canReach at h
  simp at h
  specialize h ([List.get c (Fin.mk 0 isLt)])
  have walk: isWalk [List.get c { val := 0, isLt := isLt }] G := by
    apply isWalkSingleton
    rcases cycle with ⟨walk_c,_⟩
    unfold isWalk at walk_c
    rcases walk_c with ⟨walk_c,_⟩
    apply walk_c
    apply List.get_mem

  specialize h walk
  simp[cycle] at h




lemma frontRepetitionInWalkImpliesCycle (a:ℕ) (G:Graph A) (visited: List ℕ) (walk: isWalk (a::visited) G) (mem: a ∈ visited): isCycle (a::(getSubListToMember visited a mem)) G :=
by
  unfold isCycle
  simp
  have h : ¬ Nat.succ (List.length (getSubListToMember visited a mem)) < 2 := by
    push_neg
    cases h':getSubListToMember visited a mem with
    | nil =>
      have p: getSubListToMember visited a mem ≠ [] := by
        apply getSubListToMemberNonEmpty
      exact absurd h' p
    | cons hd tl =>
      simp
      rw [Nat.two_le_iff]
      simp

  simp [h]
  constructor
  cases h':getSubListToMember visited a mem with
  | nil =>
    have p: getSubListToMember visited a mem ≠ [] := by
      apply getSubListToMemberNonEmpty
    exact absurd h' p
  | cons hd tl =>
    apply isWalk_extends_successors
    rw [← h']
    apply getSubListToMemberPreservesWalk (walk:= isWalk_of_cons walk)
    unfold isWalk at walk
    rcases walk with ⟨_, conn⟩
    specialize conn (Nat.succ 0)
    simp at conn
    have g : Nat.succ 0 < List.length (a :: visited) := by
      simp
      apply Nat.succ_lt_succ
      cases visited with
      | nil =>
        simp at mem
      | cons hd' tl' =>
        simp
    specialize conn g
    have isLt: 0 < List.length visited := by
      apply Nat.lt_of_succ_lt_succ
      apply g
    have first_vis: List.get visited { val := 0, isLt := isLt} = hd := by
      cases visited with
      | nil =>
        simp at mem
      | cons hd' tl' =>
        simp [List.get_cons_zero]
        apply getSubListToMemberPreservesFront (result:=h')
    simp [first_vis] at conn
    apply conn

  apply Eq.symm
  rw [List.get_eq_iff]
  simp
  rw [getSubListToMember_length  a visited mem, List.get?_cons_succ, getSubListToMemberEndsWithElement]

lemma except_is_ok_iff_exists {A B: Type} (e: Except A B): (∃ (b:B), e = Except.ok b) ↔ Except.isOk e :=
by
  cases e with
  | error msg =>
    unfold Except.isOk
    unfold Except.toBool
    simp
  | ok u =>
    unfold Except.isOk
    unfold Except.toBool
    simp

lemma except_is_ok_of_ok {A B: Type} (b:B): Except.isOk (Except.ok b: Except A B) = true :=
by
  unfold Except.isOk
  unfold Except.toBool
  simp

lemma except_is_ok_of_error {A B: Type} (a:A) : Except.isOk (Except.error a: Except A B) = true → False:=
by
  unfold Except.isOk
  unfold Except.toBool
  simp




def foldl_except_set (f: A → HashSet B → (Except String (HashSet B))) (l: List A) (init: HashSet B): Except String (HashSet B) :=
  match l with
  | [] => Except.ok init
  | hd::tl =>
    match f hd init with
    | Except.error msg => Except.error msg
    | Except.ok S => foldl_except_set f tl S

lemma foldl_except_set_subset [Hashable B] (f: A → HashSet B → (Except String (HashSet B))) (l: List A) (init: HashSet B) (subs: ∀ (S S':HashSet B ) (a:A), a ∈ l →  f a S = Except.ok S' → S ⊆ S')(S: HashSet B) (get_S: foldl_except_set f l init = Except.ok S) : init ⊆ S :=
by
  revert S
  induction l generalizing init with
  | nil =>
    intro S
    unfold foldl_except_set
    simp
    intro h
    rw [h]
    apply HashSet.Subset.refl
  | cons hd tl ih =>
    intro S
    unfold foldl_except_set
    intro h
    cases h':f hd init with
    | error e =>
      simp[h'] at h
    | ok S' =>
      simp [h'] at h
      apply HashSet.Subset.trans (S2:= S')
      have hd_mem: hd ∈ hd::tl := by
        simp
      apply subs init S' hd hd_mem h'
      apply ih S'
      intro T T' a' a_tl
      apply subs
      simp [a_tl]
      apply h

lemma foldl_except_set_contains_list_map [Hashable B] [DecidableEq B] (f: A → HashSet B → (Except String (HashSet B))) (l: List A) (init: HashSet B) (subs: ∀ (S S':HashSet B ) (a:A), a ∈ l →  f a S = Except.ok S' → S ⊆ S')(map: A → B) (map_prop: ∀ (a:A) (S S':HashSet B ), f a S  = Except.ok S' →  S'.contains (map a) ) (T: HashSet B) (get_T: foldl_except_set f l init = Except.ok T) : ∀ (b:B), b ∈  (List.map map l) → T.contains b :=
by
  revert T
  induction l generalizing init with
  | nil =>
    simp
  | cons hd tl ih =>
    intro T get_T b b_mem
    unfold foldl_except_set at get_T
    cases f_hd: f hd init with
    | error e =>
      simp [f_hd] at get_T
    | ok S =>
      simp [f_hd] at get_T
      unfold List.map at b_mem
      simp at b_mem
      have subs':  ∀ (S S' : HashSet B) (a : A), a ∈ tl → f a S = Except.ok S' → S ⊆ S' := by
        intro S S' a a_tl f_a
        apply subs S S' a
        simp [a_tl]
        apply f_a
      cases b_mem with
      | inl b_hd =>
        have S_T: S ⊆ T := by
          apply foldl_except_set_subset (subs:=subs') (get_S:=get_T)
        rw [HashSet.Subset.Iff] at S_T
        apply S_T
        rw [b_hd]
        apply map_prop hd init S f_hd
      | inr b_tl =>
        apply ih
        apply subs'
        apply get_T
        simp
        apply b_tl

lemma foldl_except_set_preserves_p [Hashable B] (f: A → HashSet B → (Except String (HashSet B))) (p: B → Prop) (l: List A) (init: HashSet B) (init_prop: ∀ (b:B), init.contains b → p b) (S: HashSet B) (h: foldl_except_set f l init = Except.ok S ) (f_prev: ∀ (a:A) (S S': HashSet B), (∀ (b:B), S.contains b → p b) → f a S = Except.ok S' → (∀ (b:B), S'.contains b → p b) ): ∀ (b:B), S.contains b → p b :=
by
  induction l generalizing init with
  | nil =>
    unfold foldl_except_set at h
    simp at h
    intro b
    rw [← h]
    apply init_prop
  | cons hd tl ih =>
    unfold foldl_except_set at h
    cases f_hd:f hd init with
    | error e=>
      simp [f_hd] at h
    | ok S' =>
      simp [f_hd] at h
      specialize ih S'
      apply ih
      apply f_prev
      apply init_prop
      apply f_hd
      apply h



lemma foldl_except_set_is_ok [Hashable B] (f: A → HashSet B → (Except String (HashSet B))) (p: B → Prop) (l: List A) (init: HashSet B) (init_prop: ∀ (b:B), init.contains b → p b) (f_ignore_B: ∀ (a:A) (S S': HashSet B), (∀ (b:B), S.contains b → p b) →  (∀ (b:B), S'.contains b → p b) → (Except.isOk (f a S) ↔ Except.isOk (f a S'))) (f_prev: ∀ (a:A) (S S': HashSet B), (∀ (b:B), S.contains b → p b) → f a S = Except.ok S' → (∀ (b:B), S'.contains b → p b) ): (∃ (S: HashSet B), foldl_except_set f l init = Except.ok S) ↔ ∀ (a:A), a ∈ l → Except.isOk (f a init) :=
by
  induction l generalizing init with
  | nil =>
    unfold foldl_except_set
    simp
  | cons hd tl ih =>
    unfold foldl_except_set
    split
    simp
    rename_i msg h
    rw [h]
    unfold Except.isOk
    unfold Except.toBool
    simp

    rename_i e S h
    rw [ih]
    simp
    rw [h]
    simp [except_is_ok_of_ok]
    constructor
    intro h' a a_tl
    specialize f_ignore_B a init S
    rw [f_ignore_B]
    apply h'
    exact a_tl
    apply init_prop
    apply f_prev hd init S
    exact init_prop
    exact h

    intro h' a a_tl
    specialize f_ignore_B a init S
    rw [← f_ignore_B]
    apply h' a a_tl
    apply init_prop
    all_goals{
    apply f_prev hd init S
    exact init_prop
    exact h
    }


def addElementIfOk [Hashable A] (e: Except B (HashSet A)) (a:A): Except B (HashSet A) :=
  match e with
  | Except.ok S => Except.ok (S.insert a)
  | Except.error msg => Except.error msg

lemma addElementIfOk_exists_ok [Hashable A] (e: Except String (HashSet A)) (a:A): (∃ (S: HashSet A), addElementIfOk e a = Except.ok S) ↔ ∃ (S:HashSet A), e = Except.ok S :=
by
  constructor
  intro h
  rcases h with ⟨S, add⟩
  unfold addElementIfOk at add
  cases e with
  | ok S' =>
    use S'
  | error e =>
    simp at add

  intro h
  rcases h with ⟨S, e_S⟩
  rw [e_S]
  simp [addElementIfOk]

lemma addElementIfOk_exists_ok' [Hashable A] (e: Except String (HashSet A)) (a:A) (S: HashSet A): addElementIfOk e a = Except.ok S ↔ ∃ (S': HashSet A), S = S'.insert a ∧ e = Except.ok S' :=
by
  cases e with
  | error e =>
    unfold addElementIfOk
    simp
  | ok u =>
    unfold addElementIfOk
    simp [eq_comm]


lemma canReachLemma (a:ℕ) (G: Graph A) (mem: a ∈ G.vertices) (f: A → List A → Except String Unit): (∀ (b : ℕ) (reach: canReach a b G), f (G.label b (canReachMem reach)) (Graph.successorLabels G b (canReachMem reach)) = Except.ok ()) ↔ (∀ (b: ℕ), b ∈ G.successors a → (∀ (c : ℕ) (reach: canReach b c G), f (G.label c (canReachMem reach)) (Graph.successorLabels G c (canReachMem reach)) = Except.ok ())) ∧ f (G.label a mem) (G.successorLabels a mem) = Except.ok () :=
by

  constructor
  intro h
  constructor
  intro b b_succ
  intro c reach_c
  apply h
  unfold canReach
  unfold canReach at reach_c
  rcases reach_c with ⟨p, neq, walk, get_c, get_b⟩
  use p++[a]
  have neq': p++[a] ≠ [] := by
    simp
  use neq'
  constructor
  unfold isWalk
  constructor
  intro a' a'p
  simp at a'p
  cases a'p with
  | inl a'p =>
    apply isWalkImplSubset' walk a' a'p
  | inr a'p =>
    rw [a'p]
    apply mem
  intro i i_zero i_len
  simp at i_len
  rw [← Nat.succ_eq_add_one, Nat.lt_succ_iff_lt_or_eq] at i_len
  unfold isWalk at walk
  rcases walk with ⟨subs,conn⟩
  cases i_len with
  | inl i_lt_p =>
    rw [List.get_append_left, List.get_append_left]
    apply conn i i_zero i_lt_p
  | inr i_p =>
    simp [i_p]
    rw [List.get_append_left, List.get_append_right]
    simp[get_b]
    apply b_succ
    simp
    simp
    cases p with
    | nil =>
      simp at i_p
      rw [i_p] at i_zero
      simp at i_zero
    | cons hd tl =>
      simp

  constructor
  rw [List.get_append_left]
  apply get_c
  rw [List.get_append_right]
  simp
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    simp
  simp

  -- f at same spot
  apply h
  apply canReach_refl a G mem

  -- back direction
  intro h
  intro b reach
  unfold canReach at reach
  rcases reach with ⟨p, neq, walk, get_b, get_a⟩
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    cases tl with
    | nil =>
      simp at get_a
      simp at get_b
      simp_rw [← get_b, get_a]
      apply And.right h
    | cons hd' tl' =>
      rcases h with ⟨left,_⟩
      have isLt: Nat.pred (Nat.pred (hd::hd'::tl').length) < (hd::hd'::tl').length := by
        simp
        apply Nat.lt_trans (m:= Nat.succ tl'.length)
        simp
        simp
      have succ: List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt) ∈ G.successors a := by
        rw [← get_a]
        unfold isWalk at walk
        rcases walk with ⟨_,conn⟩
        apply conn
        simp
      specialize left (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) succ
      apply left
      unfold canReach
      use (getSubListToMember (hd::hd'::tl') (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) (List.get_mem (hd::hd'::tl') (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt))
      simp
      constructor
      apply getSubListToMemberPreservesWalk (hd::hd'::tl') (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) (List.get_mem (hd::hd'::tl') (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt) G walk
      constructor
      constructor
      rw [← get_b]
      apply Eq.symm
      apply getSubListToMemberPreservesFront'
      apply getSubListToMemberNonEmpty
      rw [List.get_eq_iff]
      apply getSubListToMemberEndsWithElement

lemma allTrueIfAllCanReachTrue (f: A → List A → Except String Unit) (G: Graph A): (∀ (a:ℕ) (mem: a ∈ G.vertices), f (G.label a mem) (G.successorLabels a mem) = Except.ok ()) ↔ ∀ (a:ℕ ), a ∈ G.vertices → ∀ (b:ℕ) (reach: canReach a b G), f (G.label b (canReachMem reach)) (G.successorLabels b (canReachMem reach)) = Except.ok () :=
by
  constructor
  intro h a _ b reach
  apply h

  intro h a a_mem
  apply h a a_mem
  apply canReach_refl
  apply a_mem

lemma not_mem_of_empty_intersection {l1 l2: List A} (inter: l1 ∩ l2 = ∅): ∀ (a:A), a ∈ l1 → ¬ a ∈ l2 :=
by
  intro a a_l1
  by_contra a_l2
  have h: a ∈ l1 ∧ a ∈ l2 := by
    apply And.intro a_l1 a_l2
  rw [← List.mem_inter_iff] at h
  rw [inter] at h
  simp at h

lemma isWalkImplMem {a: ℕ} {G: Graph A} {currWalk: List ℕ} (walk: isWalk (a::currWalk) G): a ∈ G.vertices := by
  unfold isWalk at walk
  apply And.left walk
  simp

def dfs_step (a: ℕ) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List ℕ) (walk: isWalk (a::currWalk) G) (not_mem: ¬ (a ∈ currWalk)) (visited: HashSet ℕ) : Except String (HashSet ℕ) :=
  if visited.contains a
  then Except.ok visited
  else
    match f (G.label a (isWalkImplMem walk)) (G.successorLabels a (isWalkImplMem walk)) with
    | Except.error msg => Except.error msg
    | Except.ok _ =>
      if succ_walk: (G.successors a) ∩ (a::currWalk) = []
      then

      addElementIfOk (foldl_except_set (fun ⟨x, _h⟩ S =>
        dfs_step x G f (a::currWalk) (isWalk_extends_successors walk x _h) (not_mem_of_empty_intersection succ_walk x _h) S) (G.successors a).attach visited) a
      else
        Except.error "Cycle detected"
termination_by Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)
decreasing_by
  simp_wf
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  simp
  use a
  constructor
  intro _
  left
  rfl

  rw [Finset.subset_iff]
  intro b
  simp
  intro h
  cases h with
  | inl h =>
    rw [h]
    constructor
    have mem_walk: a ∈ a::currWalk := by
      simp
    apply isWalkImplSubset' walk a mem_walk
    apply not_mem
  | inr h =>
    rcases h with ⟨left,right⟩
    push_neg at right
    simp [left,right]



lemma dfs_step_subset (a: ℕ) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List ℕ ) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet ℕ): ∀ (S:HashSet ℕ ), dfs_step a G f currWalk walk not_mem visited = Except.ok S → visited ⊆ S :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)  with n ih generalizing a currWalk visited

  --base case: impossible as a is not in walk and yet everything must be in the walk
  rw[Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices := by
    apply isWalkImplSubset' walk
    simp
  specialize h a_G
  exact absurd h not_mem

  intro S get_S
  have a_mem: a ∈ G.vertices := by
    apply isWalkImplSubset' walk
    simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) = n := by
    rw [Nat.succ_eq_add_one] at h
    have h': List.toFinset G.vertices \ List.toFinset currWalk = insert a (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) := by
      rw [Finset.ext_iff]
      simp
      intro a'
      by_cases a_a': a = a'
      simp [a_a']
      rw [← a_a']
      constructor
      apply a_mem
      apply not_mem
      constructor
      intro ha
      right
      simp [ha]
      apply Ne.symm a_a'
      intro ha
      cases ha with
      | inl a_a =>
        exact absurd (Eq.symm a_a) a_a'
      | inr ha =>
        rw [not_or] at ha
        simp [ha]
    rw [h', Finset.card_insert_of_not_mem, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one, Nat.succ_inj'] at h
    apply h
    simp

  unfold dfs_step at get_S
  by_cases a_vis: visited.contains a
  simp [a_vis] at get_S
  rw [get_S]
  apply HashSet.Subset.refl

  simp [a_vis] at get_S
  cases f_a: f (G.label a (isWalkImplMem walk)) (G.successorLabels a (isWalkImplMem walk)) with
  | error e=>
    simp[f_a] at get_S
  | ok _ =>
    simp [f_a] at get_S
    have int_walk_succ: Graph.successors G a ∩ (a :: currWalk) = [] := by
      by_contra p
      simp [p] at get_S
    simp [int_walk_succ] at get_S
    rw [addElementIfOk_exists_ok'] at get_S
    rcases get_S with ⟨S', S_S', foldl_result⟩
    rw [S_S']
    have visit_S': visited ⊆ S' := by
      apply foldl_except_set_subset (l:=(G.successors a).attach) (get_S:= foldl_result)
      simp
      intro T T' x x_succ
      apply ih
      apply card
    -- end have visit_S'
    rw [HashSet.Subset.Iff]
    intro x x_vis
    rw [HashSet.contains_insert]
    left
    rw [HashSet.Subset.Iff] at visit_S'
    apply visit_S' x x_vis

lemma dfs_step_returns_root_element (a: ℕ) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List ℕ) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet ℕ) (S:HashSet ℕ) (get_S:dfs_step a G f currWalk walk not_mem visited = Except.ok S): S.contains a :=
by
  unfold dfs_step at get_S
  by_cases a_visit: visited.contains a
  simp [a_visit] at get_S
  rw [get_S] at a_visit
  apply a_visit

  simp [a_visit] at get_S
  cases f_a: f (G.label a (isWalkImplMem walk)) (G.successorLabels a (isWalkImplMem walk)) with
  | error e=>
    simp[f_a] at get_S
  | ok _ =>
    simp[f_a] at get_S
    by_cases h : Graph.successors G a ∩ (a :: currWalk) = []
    simp [h] at get_S
    rw [addElementIfOk_exists_ok'] at get_S
    rcases get_S with ⟨S', S_S',_⟩
    rw [S_S']
    rw [HashSet.contains_insert]
    right
    rfl

    simp [h] at get_S

lemma dfs_step_preserves_notReachesCycleAndCounterExample (a: ℕ) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List ℕ ) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet ℕ ) (visited_prop: ∀ (a:ℕ ), visited.contains a → ¬ reachesCycle a G ∧ ∀ (b:ℕ) (reach: canReach a b G), f (G.label b (canReachMem reach)) (G.successorLabels b (canReachMem reach)) = Except.ok ()) (S: HashSet ℕ) (get_S: dfs_step a G f currWalk walk not_mem visited = Except.ok S): ∀ (a:ℕ),  S.contains a → ¬ reachesCycle a G ∧ ∀ (b:ℕ)(reach: canReach a b G ), f (G.label b (canReachMem reach)) (G.successorLabels b (canReachMem reach)) = Except.ok () :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)  with n ih generalizing a currWalk visited S

  --base case: impossible as a is not in walk and yet everything must be in the walk
  rw[Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices := by
    apply isWalkImplSubset' walk
    simp
  specialize h a_G
  exact absurd h not_mem

  --step
  have a_mem: a ∈ G.vertices := by
    apply isWalkImplSubset' walk
    simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) = n := by
    rw [Nat.succ_eq_add_one] at h
    have h': List.toFinset G.vertices \ List.toFinset currWalk = insert a (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) := by
      rw [Finset.ext_iff]
      simp
      intro a'
      by_cases a_a': a = a'
      simp [a_a']
      rw [← a_a']
      constructor
      apply a_mem
      apply not_mem
      constructor
      intro ha
      right
      simp [ha]
      apply Ne.symm a_a'
      intro ha
      cases ha with
      | inl a_a =>
        exact absurd (Eq.symm a_a) a_a'
      | inr ha =>
        rw [not_or] at ha
        simp [ha]
    rw [h', Finset.card_insert_of_not_mem, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one, Nat.succ_inj'] at h
    apply h
    simp

  unfold dfs_step at get_S
  by_cases a_visit: visited.contains a
  simp [a_visit] at get_S
  simp [← get_S]
  apply visited_prop

  simp [a_visit] at get_S
  cases f_a: f (G.label a (isWalkImplMem walk)) (G.successorLabels a (isWalkImplMem walk)) with
  | error e =>
    simp [f_a] at get_S
  | ok _ =>
    simp [f_a] at get_S
    have inter: Graph.successors G a ∩ (a :: currWalk) = [] := by
      by_contra p
      simp [p] at get_S
    simp [inter] at get_S
    rw [addElementIfOk_exists_ok'] at get_S
    rcases get_S with ⟨S', S_S', foldl_result⟩
    have preserve_S': ∀ (a : ℕ ), S'.contains a → ¬reachesCycle a G ∧ ∀ (b : ℕ) (reach:canReach a b G), f (G.label b (canReachMem reach)) (G.successorLabels b (canReachMem reach)) = Except.ok () := by
      apply foldl_except_set_preserves_p (init_prop:=visited_prop) (h:= foldl_result)
      simp
      intro b b_succ T T' T_prop dfs_T'
      specialize ih b (a::currWalk) (isWalk_extends_successors walk b b_succ) (not_mem_of_empty_intersection inter b b_succ) T T_prop T' dfs_T' card
      apply ih

    --split cases
    intro b
    rw [S_S']
    intro b_mem
    rw [HashSet.contains_insert] at b_mem
    cases b_mem with
    | inl b_S' =>
      apply preserve_S' b b_S'
    | inr b_a =>
      have b_mem: b ∈ G.vertices := by
        rw [← b_a]
        apply a_mem
      rw [NotreachesCycleIffSuccessorsNotReachCycle (mem:=b_mem), canReachLemma (mem:=b_mem)]
      simp [← b_a, f_a]
      rw [← forall_and]
      intro a'
      rw [← imp_and]
      intro a'_succ
      apply preserve_S'
      apply foldl_except_set_contains_list_map (get_T:=foldl_result) (map:= fun ⟨x,_h⟩ => x)
      simp
      intro T T' x x_succ
      apply dfs_step_subset

      simp
      intro x x_succ
      apply dfs_step_returns_root_element

      simp
      apply a'_succ



lemma dfs_step_sematics (a: ℕ) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List ℕ ) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet ℕ ) (visited_prop: ∀ (a:ℕ ), visited.contains a → ¬ reachesCycle a G ∧ ∀ (b:ℕ ) (reach: canReach a b G), f (G.label b (canReachMem reach)) (G.successorLabels b (canReachMem reach)) = Except.ok ()):  Except.isOk (dfs_step a G f currWalk walk not_mem visited) ↔  ¬ reachesCycle a G ∧ (∀ (b:ℕ ) (reach: canReach a b G ), f (G.label b (canReachMem reach)) (G.successorLabels b (canReachMem reach)) = Except.ok ()) :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)  with n ih generalizing a currWalk visited

  --base case: impossible as a is not in walk and yet everything must be in the walk
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices := by
    apply isWalkImplSubset' walk
    simp
  specialize h a_G
  exact absurd h not_mem

  --step
  have a_mem: a ∈ G.vertices := by
    apply isWalkImplSubset' walk
    simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) = n := by
    rw [Nat.succ_eq_add_one] at h
    have h': List.toFinset G.vertices \ List.toFinset currWalk = insert a (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) := by
      rw [Finset.ext_iff]
      simp
      intro a'
      by_cases a_a': a = a'
      simp [a_a']
      rw [← a_a']
      constructor
      apply a_mem
      apply not_mem
      constructor
      intro ha
      right
      simp [ha]
      apply Ne.symm a_a'
      intro ha
      cases ha with
      | inl a_a =>
        exact absurd (Eq.symm a_a) a_a'
      | inr ha =>
        rw [not_or] at ha
        simp [ha]
    rw [h', Finset.card_insert_of_not_mem, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one, Nat.succ_inj'] at h
    apply h
    simp

  constructor
  intro h'
  rw [← except_is_ok_iff_exists] at h'
  rcases h' with ⟨S, dfs_get⟩
  apply dfs_step_preserves_notReachesCycleAndCounterExample (visited_prop:=visited_prop)
  apply dfs_get
  apply dfs_step_returns_root_element (get_S:=dfs_get)

  intro h'
  unfold dfs_step
  by_cases a_visit: visited.contains a
  simp [a_visit]
  apply except_is_ok_of_ok

  simp[a_visit]
  rcases h' with ⟨reach_cycle, reach_f⟩
  have f_a: f (G.label a (isWalkImplMem walk)) (G.successorLabels a (isWalkImplMem walk)) = Except.ok () := by
    apply reach_f
    apply canReach_refl a G a_mem
  simp [f_a]

  have succ_walk: Graph.successors G a ∩ (a :: currWalk) = [] := by
    cases inter: Graph.successors G a ∩ (a :: currWalk) with
    | nil =>
      simp
    | cons hd tl =>
      have hd_mem: hd ∈ G.successors a ∧ hd ∈ (a::currWalk) := by
        rw [← List.mem_inter_iff, inter]
        simp
      rcases hd_mem with ⟨hd_succ, hd_a_currWalk⟩

      have cycle_hd: isCycle (hd::(getSubListToMember (a::currWalk) hd hd_a_currWalk)) G := by
        apply frontRepetitionInWalkImpliesCycle
        apply isWalk_extends_successors walk hd hd_succ

      have reachesCycleHd: reachesCycle hd G := by
        unfold reachesCycle
        use hd::(getSubListToMember (a::currWalk) hd hd_a_currWalk)
        constructor
        apply cycle_hd
        use hd
        simp
        apply canReach_refl
        apply G.complete
        apply a_mem
        apply hd_succ

      rw [NotreachesCycleIffSuccessorsNotReachCycle (mem:= a_mem)] at reach_cycle
      specialize reach_cycle hd hd_succ
      exact absurd reachesCycleHd reach_cycle

  simp [succ_walk]
  rw [← except_is_ok_iff_exists, addElementIfOk_exists_ok,foldl_except_set_is_ok (init_prop:=visited_prop)]
  simp
  intro b b_succ
  have b_mem: b ∈ G.vertices := by
    apply G.complete a a_mem b b_succ
  specialize ih b (a::currWalk) (isWalk_extends_successors walk b b_succ) (not_mem_of_empty_intersection succ_walk b b_succ) visited visited_prop card
  rw [ih]
  constructor
  rw [NotreachesCycleIffSuccessorsNotReachCycle (mem:= a_mem)] at reach_cycle
  apply reach_cycle b b_succ
  rw [canReachLemma (mem:=a_mem)] at reach_f
  apply And.left (reach_f )
  apply b_succ

  simp
  intro b b_succ S S' S_prop S'_prop
  rw [ih, ih]
  apply S'_prop
  apply card
  apply S_prop
  apply card

  simp
  intro b b_succ S S' S_prop
  apply dfs_step_preserves_notReachesCycleAndCounterExample
  apply S_prop

def isOkOrMessage (e: Except String A): Except String Unit :=
  match e with
  | Except.error msg => Except.error msg
  | Except.ok _ => Except.ok ()

lemma isOkOrMessageOkIffExceptionIsOk (e: Except String A): isOkOrMessage e = Except.ok () ↔ ∃ (a:A), e = Except.ok a :=
by
  unfold isOkOrMessage
  cases e with
  | error msg =>
    simp
  | ok S =>
    simp

def dfs (G: Graph A) (f: A → List A → Except String Unit) : Except String Unit :=
  isOkOrMessage (foldl_except_set (fun ⟨x,_h⟩ S => dfs_step x G f [] (isWalkSingleton G x _h) (List.not_mem_nil x) S) G.vertices.attach HashSet.empty )

lemma dfs_semantics (G: Graph A) (f: A → List A → Except String Unit): dfs G f = Except.ok () ↔ isAcyclic G ∧ ∀ (a:ℕ)(mem: a ∈ G.vertices), f (G.label a mem) (G.successorLabels a mem ) = Except.ok () :=
by
  unfold dfs
  rw [isOkOrMessageOkIffExceptionIsOk, acyclicIffAllNotReachCycle, allTrueIfAllCanReachTrue]
  rw [foldl_except_set_is_ok]
  simp [← forall_and, ← imp_and, ← forall_and]
  constructor
  intro h a a_mem
  specialize h a a_mem
  rw [dfs_step_sematics] at h
  apply h
  intro a a_mem
  exfalso
  apply HashSet.empty_contains a a_mem
  intro h a a_mem
  rw [dfs_step_sematics]
  specialize h a a_mem
  apply h
  intro a a_mem
  exfalso
  apply HashSet.empty_contains a a_mem


  use (fun x => ¬reachesCycle x G ∧ ∀ (b : ℕ)(reach: canReach x b G), f (G.label b (canReachMem reach)) (Graph.successorLabels G b (canReachMem reach)) = Except.ok ())
  simp [HashSet.empty_contains]

  simp
  intro a a_mem S S' S_prop S'_prop
  rw [dfs_step_sematics (visited_prop:=S_prop), dfs_step_sematics (visited_prop:=S'_prop)]

  simp
  intro a _succ S S' S_prop get_S'
  apply dfs_step_preserves_notReachesCycleAndCounterExample (visited_prop:=S_prop)
  apply get_S'


def extractTree (a: ℕ) (G: Graph A) (mem: a ∈ G.vertices) (acyclic: isAcyclic G): tree A :=
  tree.node (G.label a mem) (List.map (fun ⟨x, _h⟩ => extractTree x G (G.complete a mem x _h) acyclic) (G.successors a).attach)
termination_by Finset.card (globalSuccessors a G)
decreasing_by
  simp_wf
  apply Finset.card_lt_card
  apply globalSuccessorsSSubsetWhenAcyclicAndSuccessor
  apply acyclic
  apply _h
  apply mem


lemma rootOfExtractTree (a:ℕ ) (G: Graph A) (mem: a ∈ G.vertices) (acyclic: isAcyclic G): root (extractTree a G mem acyclic ) = (G.label a mem) :=
by
  unfold extractTree
  unfold root
  simp

variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

def locallyValid (P: program τ) (d: database τ) (v: ℕ) (G: Graph (groundAtom τ)) (mem: v ∈ G.vertices): Prop :=
 (∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding r g = {head:= G.label v mem, body:= (G.successorLabels v mem) }) ∨ ((G.successors v) = [] ∧ d.contains (G.label v mem))

def localValidityCheck (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (l: List (groundAtom τ)) (a: groundAtom τ) : Except String Unit :=
  if l.isEmpty
  then
    if d.contains a
    then Except.ok ()
    else checkRuleMatch m (groundRule.mk a l)
  else
    checkRuleMatch m (groundRule.mk a l)

lemma List.isEmpty_map{A B: Type} (l: List A) (f: A → B): l.isEmpty = true ↔ (l.map f).isEmpty = true := by
  cases l with
  | nil =>
    unfold map
    simp
  | cons hd tl =>
    unfold map
    simp

lemma List.isEmpty_attach {A: Type} (l: List A): l.isEmpty = true ↔ l.attach.isEmpty = true := by
  cases l with
  | nil =>
    unfold attach
    simp
  | cons hd tl =>
    unfold attach
    unfold pmap
    simp

lemma SuccessorsEmptyIffSuccessorLabelsEmpty (G: Graph (groundAtom τ)) (a: ℕ) (mem: a ∈ G.vertices): (G.successors a).isEmpty = true ↔ (G.successorLabels a mem).isEmpty := by
  unfold Graph.successorLabels
  unfold PreGraph.successorLabels
  simp
  rw [← List.isEmpty_map, ← List.isEmpty_attach]
  unfold Graph.successors
  simp



lemma localValidityCheckUnitIffLocallyValid (P: List (rule τ)) (d: database τ) (G: Graph (groundAtom τ)) (a: ℕ) (mem: a ∈ G.vertices) (l: List (groundAtom τ)) (l_prop: l = G.successorLabels a mem) :  localValidityCheck (parseProgramToSymbolSequenceMap P (fun _ => [])) d l (G.label a mem) = Except.ok () ↔ locallyValid P.toFinset d a G mem :=
by
  unfold locallyValid
  unfold localValidityCheck
  rw [l_prop]
  simp
  constructor

  intro h
  by_cases empty: List.isEmpty (G.successors a) = true
  rw [SuccessorsEmptyIffSuccessorLabelsEmpty (mem:=mem)] at empty
  simp [empty] at h
  rw [← SuccessorsEmptyIffSuccessorLabelsEmpty (mem:=mem)] at empty
  by_cases db: d.contains (G.label a mem)
  right
  constructor
  rw [List.isEmpty_iff_eq_nil] at empty
  apply empty
  apply db
  simp at db
  specialize h db
  rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) ] at h
  left
  simp at h
  apply h

  rw [SuccessorsEmptyIffSuccessorLabelsEmpty (mem:= mem)] at empty
  simp [empty] at h
  rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P)] at h
  left
  simp at h
  apply h

  intro h
  by_cases empty: List.isEmpty (Graph.successors G a)
  rw [SuccessorsEmptyIffSuccessorLabelsEmpty (mem:=mem)] at empty
  rw [if_pos empty]
  by_cases db: d.contains (G.label a mem)
  simp [db]
  simp [db]
  cases h with
  | inl ruleCase =>
    rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P)]
    simp
    apply ruleCase
  | inr dbCase =>
    rcases dbCase with ⟨_, n_db⟩
    exact absurd n_db db

  rw [SuccessorsEmptyIffSuccessorLabelsEmpty (mem:=mem)] at empty
  simp [empty]
  cases h with
  | inl ruleCase =>
    rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P)]
    simp
    apply ruleCase
  | inr dbCase =>
    rcases dbCase with ⟨n_empty, _⟩
    rw [← List.isEmpty_iff_eq_nil] at n_empty
    rw [← SuccessorsEmptyIffSuccessorLabelsEmpty (mem:=mem)] at empty
    exact absurd n_empty empty


lemma extractTreeValidIffAllLocallyValidAndAcyclic (P: program τ) (d: database τ) (a: ℕ ) (G: Graph (groundAtom τ)) (acyclic: isAcyclic G) (mem: a ∈ G.vertices) (valid: ∀ (a: ℕ)(mem: a ∈ G.vertices), locallyValid P d a G mem): isValid P d (extractTree a G mem acyclic) :=
by
  induction' h:(globalSuccessors a G).card using Nat.strongInductionOn with n ih generalizing a
  unfold extractTree
  unfold isValid
  have valid_a: locallyValid P d a G mem := by
    apply valid a mem
  unfold locallyValid at valid_a
  cases valid_a with
  | inl ruleCase =>
    rcases ruleCase with ⟨r,g, rP, ground_r⟩
    left
    use r
    use g
    constructor
    apply rP
    constructor
    rw [ground_r, groundRuleEquality]
    simp
    apply List.ext_get
    rw [List.length_map, List.length_attach]
    unfold Graph.successorLabels
    unfold PreGraph.successorLabels
    unfold Graph.successors
    simp

    intro n h1 h2
    simp
    rw [rootOfExtractTree]
    unfold Graph.successorLabels
    unfold PreGraph.successorLabels
    unfold Graph.label
    unfold Graph.successors
    simp

    rw [List.forall_iff_forall_mem]
    simp
    intro t b b_mem extract_b
    specialize ih (globalSuccessors b G).card
    rw [← h] at ih
    rw [← extract_b]
    apply ih
    apply Finset.card_lt_card
    apply globalSuccessorsSSubsetWhenAcyclicAndSuccessor _ _ _ acyclic b_mem mem
    rfl
  | inr dbCase =>
    right
    simp
    exact dbCase

lemma verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (P: program τ) (d: database τ)  (G: Graph (groundAtom τ)) (acyclic: isAcyclic G)  (valid: ∀ (a: ℕ) (mem: a ∈ G.vertices), locallyValid P d a G mem): List.toSet G.labels ⊆ proofTheoreticSemantics P d :=
by
  rw [Set.subset_def]
  intro a a_mem
  rw [← List.toSet_mem] at a_mem
  unfold Graph.labels at a_mem
  unfold PreGraph.labels at a_mem
  simp at a_mem
  rcases a_mem with ⟨x, x_a⟩
  rw [List.mem_iff_get] at x_a
  rcases x_a with ⟨f, f_get⟩
  have f_mem: f.val ∈ G.vertices := by
    unfold Graph.vertices
    unfold PreGraph.vertices
    rw [Array.toList_eq, ← Array.mem_def]
    rw [Array.enum_mem]
    simp at f
    apply f.2


  unfold proofTheoreticSemantics
  simp
  use extractTree f.val G f_mem acyclic
  constructor
  rw [rootOfExtractTree]
  unfold Graph.label
  unfold PreGraph.label
  unfold Array.get
  simp[f_get]

  apply extractTreeValidIffAllLocallyValidAndAcyclic
  apply valid
