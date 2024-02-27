import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation
import Mathlib.Data.List.Card
import Mathlib.Data.Finset.Card


structure Graph (A: Type) where
  (vertices: List A)
  (predecessors: A → List A)
  (complete: ∀ (a:A), a ∈ vertices →  ∀ (a':A), a' ∈ predecessors a → a' ∈ vertices)

section dfs
variable {A: Type}[DecidableEq A] {B: Type} [DecidableEq B]
open Lean


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


def isWalk (l: List A) (G: Graph A): Prop :=
 ( ∀ (a:A), a ∈ l → a ∈ G.vertices ) ∧ ∀ (i: ℕ), i > 0 → ∀ (g: i < l.length), l.get (Fin.mk i.pred (pred_lt i l.length g)) ∈ G.predecessors (l.get (Fin.mk i g) )

 lemma isWalkSingleton (G: Graph A) (a:A) (mem: a ∈ G.vertices): isWalk [a] G :=
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

def isCycle (l: List A) (G: Graph A): Prop :=
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

lemma IsWalkOfisCycle (l: List A) (G: Graph A) (h: isCycle l G): isWalk l G :=
by
  unfold isCycle at h
  by_cases h' : List.length l < 2
  simp [h'] at h

  simp [h'] at h
  simp [h]

def isAcyclic (G: Graph A) := ∀ (l: List A), ¬ isCycle l G





lemma isWalk_extends_predecessors {a: A} {l: List A} {G: Graph A} (walk: isWalk (a::l) G): ∀ (b:A), b ∈ (G.predecessors a) → isWalk (b::a::l) G :=
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
      have g: Nat.succ k < List.length (a :: l)
      rw [Nat.succ_lt_succ_iff] at i_len
      simp
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      apply i_len
      specialize connected g
      apply connected

lemma isWalkImplSubset {l: List A} {G: Graph A} (walk: isWalk l G ): l.toFinset ⊆ G.vertices.toFinset :=
by
  rw [Finset.subset_iff]
  unfold isWalk at walk
  rcases walk with ⟨h,_⟩
  simp [List.mem_toFinset]
  apply h

lemma isWalkImplSubset' {l: List A} {G: Graph A} (walk: isWalk l G ): ∀ (a:A), a ∈ l → a ∈ G.vertices :=
by
  unfold isWalk at walk
  rcases walk with ⟨walk,_⟩
  apply walk

lemma isWalk_of_cons {a: A} {l:List A} {G:Graph A} (walk: isWalk (a::l) G): isWalk l G :=
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
  have g:  Nat.succ i < List.length (a :: l)
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

def canReach (a b: A) (G: Graph A):= ∃ (p: List A) (neq: p ≠ []), isWalk p G ∧ p.get (Fin.mk 0 (getFirstForNonequal_isLt p neq)) = a ∧ p.get (Fin.mk p.length.pred (getLastForNonequal_isLt p neq)) = b

lemma canReach_refl (a:A) (G: Graph A) (mem: a ∈ G.vertices): canReach a a G :=
by
  unfold canReach
  use [a]
  have neq: [a] ≠ []
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

-- added based on https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/finset.2Efilter
noncomputable def Finset.filter_nc (p: A → Prop) (S: Finset A):= @Finset.filter A p (Classical.decPred p) S

lemma Finset.mem_filter_nc (a:A) (p: A → Prop) (S: Finset A): a ∈ Finset.filter_nc p S ↔ p a ∧ a ∈ S :=
by
  unfold filter_nc
  have dec: DecidablePred p
  apply Classical.decPred
  simp [Finset.mem_filter]
  rw [And.comm]

noncomputable def globalPredecessors (b:A) (G: Graph A): Finset A := Finset.filter_nc (fun a => canReach a b G) G.vertices.toFinset


lemma isWalkExtendBack (p: List A) (a: A) (G: Graph A) (walk: isWalk p G) (nonempty_p: p ≠ []) (mem: a ∈ G.vertices) (backExtend: p.get (Fin.mk p.length.pred (getLastForNonequal_isLt p nonempty_p)) ∈ G.predecessors a): isWalk (p++[a]) G :=
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
  have i_original_pred: i.pred < p.length
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
    simp at i_len
    rw [← Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at i_len
    simp at h
    rw [← not_lt] at h
    exact absurd i_len h

lemma globalPredecessorsSubsetWhenPredecessor (a b:A) (G: Graph A) (mem: a ∈ G.vertices) (pred: b ∈ G.predecessors a): globalPredecessors b G ⊆ globalPredecessors a G:=
by
  rw [Finset.subset_iff]
  intro x
  rw [globalPredecessors, Finset.mem_filter_nc]
  intro h
  rcases h with ⟨reach, mem'⟩
  rw [globalPredecessors, Finset.mem_filter_nc]
  constructor
  unfold canReach at *
  rcases reach with ⟨p, neq, walk, get_x, get_b⟩
  use (p++[a])
  have neq': (p++[a]) ≠ []
  simp
  use neq'
  constructor
  apply isWalkExtendBack p a G walk neq mem
  rw [get_b]
  apply pred

  constructor
  rw [List.get_append_left]
  apply get_x
  rw [List.get_append_right]
  simp
  simp
  simp
  apply mem'




lemma nodeNotInGlobalPredecessorOfPredecessorInAcyclic (a b:A) (G: Graph A) (acyclic: isAcyclic G) (pred: b ∈ G.predecessors a): ¬  a ∈ globalPredecessors b G :=
by
  by_contra p
  unfold globalPredecessors at p
  rw [Finset.mem_filter_nc] at p
  rcases p with ⟨reach,mem⟩
  unfold canReach at reach
  rcases reach with ⟨p,nonempty, walk, get_a, get_b⟩
  have cycle: isCycle (p++[a]) G
  unfold isCycle
  simp
  cases p with
  | nil =>
    simp at nonempty
  | cons hd tl =>
    have h : ¬  List.length (hd :: tl) + 1 < 2
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
    apply pred
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

lemma globalPredecessorsSSubsetWhenAcyclicAndPredecessor (G: Graph A) (a b: A) (acyclic: isAcyclic G) (pred: b ∈ G.predecessors a) (mem_a: a ∈ G.vertices): globalPredecessors b G  ⊂ globalPredecessors a G :=
by
  rw [Finset.ssubset_def]
  constructor
  apply globalPredecessorsSubsetWhenPredecessor a b G mem_a pred

  rw [Finset.subset_iff]
  simp
  use a
  constructor
  unfold globalPredecessors
  rw [Finset.mem_filter_nc]
  constructor
  unfold canReach
  use [a]
  have neq: [a] ≠ []
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

  apply nodeNotInGlobalPredecessorOfPredecessorInAcyclic
  apply acyclic
  apply pred





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
      have not_h: ¬  (getSubListToMember l a mem) = []
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




lemma getSubListToMemberPreservesWalk (l: List A) (a:A) (mem: a ∈ l) (G: Graph A) (walk: isWalk l G): isWalk (getSubListToMember l a mem) G :=
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
        have g: Nat.succ 0 < List.length (hd :: tl)
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
          have isLt: Nat.zero < List.length (getSubListToMember (hd' :: tl') a mem)
          rw [getSubListToMember_length]
          apply Nat.zero_lt_succ
          have get_result: List.get (getSubListToMember (hd' :: tl') a mem) { val := 0, isLt := isLt } = hd'
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

def reachedFromCycle (a:A) (G: Graph A):= ∃ (c: List A), isCycle c G ∧ ∃ (b: A), b ∈ c ∧ canReach b a G

lemma NotreachedFromCycleIffPredecessorsNotReachedFromCycle (a: A) (G: Graph A) (mem: a ∈ G.vertices): ¬ reachedFromCycle a G ↔ ∀ (b:A), b ∈ G.predecessors a → ¬ reachedFromCycle b G :=
by
  constructor
  intro h
  unfold reachedFromCycle at h
  simp at h
  by_contra p
  simp at p
  rcases p with ⟨x, x_pred, reach⟩
  unfold reachedFromCycle at reach
  rcases reach with ⟨c, cycle, b, b_c, reach_b_x⟩
  specialize h c cycle b b_c
  have reach_b_a: canReach b a G
  unfold canReach
  unfold canReach at reach_b_x
  rcases reach_b_x with ⟨p, neq, walk, get_b, get_x⟩
  use p++[a]
  have neq': p++[a] ≠ []
  simp
  use neq'
  constructor
  apply isWalkExtendBack p a G walk neq mem
  rw [get_x]
  apply x_pred
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
  unfold reachedFromCycle at p
  rcases p with ⟨c, cycle, b, b_c, reach_b_a⟩
  unfold canReach at reach_b_a
  rcases reach_b_a with ⟨p, neq, walk, get_b, get_a⟩
  by_cases b_pred: b ∈ G.predecessors a
  have reachCirc_b: reachedFromCycle b G
  unfold reachedFromCycle
  use c
  constructor
  apply cycle
  use b
  constructor
  apply b_c
  unfold canReach
  use [b]
  have neq': [b] ≠ []
  simp
  use neq'
  constructor
  apply isWalkSingleton
  apply G.complete
  apply mem
  apply b_pred
  simp

  specialize h b b_pred
  exact absurd reachCirc_b h

  -- b not connected with a directly
  by_cases singletonWalk: p.length = 1
  have a_b: a = b
  simp [singletonWalk] at get_a
  rw [← get_a, get_b]

  have pred_in_c: ∃ (d:A), d ∈ c ∧ d ∈ G.predecessors a
  unfold isCycle at cycle
  by_cases h : List.length c < 2
  simp [h] at cycle
  simp [h] at cycle
  rcases cycle with ⟨walk, ends⟩
  unfold isWalk at walk
  rcases walk with ⟨subs,conn⟩
  have isLt_zero_c: 0 < c.length
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
    have conn_1: Nat.pred (List.length c) > 0
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
    have g : Nat.pred (List.length c) < List.length c
    apply Nat.pred_lt
    cases c with
    | nil =>
      simp at h
    | cons hd tl =>
      simp
    specialize conn g
    have ha: List.get c (Fin.mk (Nat.pred (List.length c)) g) = b
    rw [← ends, List.get_eq_iff]
    simp
    apply get_c_b
    rw [ha, ← a_b] at conn
    have isLt': Nat.pred (Nat.pred (List.length c)) < c.length
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
    have conn1: Nat.succ m > 0
    simp
    specialize conn conn1
    rw [List.get?_eq_some] at get_c_b
    rcases get_c_b with ⟨g,c_get⟩
    specialize conn g
    have isLt: Nat.pred (Nat.succ m) < c.length
    simp
    apply Nat.lt_trans (m:= Nat.succ m)
    apply Nat.lt_succ_self
    apply g
    use List.get c (Fin.mk (Nat.pred (Nat.succ m)) isLt)
    constructor
    apply List.get_mem
    rw [c_get, ← a_b] at conn
    apply conn


  rcases pred_in_c with ⟨d, d_c, d_pred⟩
  specialize h d d_pred
  have reachCirc_d: reachedFromCycle d G
  unfold reachedFromCycle
  use c
  constructor
  apply cycle
  use d
  constructor
  apply d_c
  unfold canReach
  use [d]
  have neq': [d] ≠ []
  simp
  use neq'
  simp
  apply isWalkSingleton
  apply isWalkImplSubset' (IsWalkOfisCycle c G cycle) d d_c
  exact absurd reachCirc_d h


  have isLt: Nat.pred (Nat.pred p.length) < p.length
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

  have reachCirc: reachedFromCycle (p.get (Fin.mk (Nat.pred (Nat.pred p.length)) isLt)) G
  unfold reachedFromCycle
  use c
  constructor
  apply cycle
  use b
  constructor
  apply b_c
  unfold canReach
  have mem_p: (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) ∈ p
  apply List.get_mem

  use (getSubListToMember p (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) mem_p)
  have neq': (getSubListToMember p (List.get p (Fin.mk (Nat.pred (Nat.pred (List.length p))) isLt)) mem_p) ≠ []
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

  have gt_zero:  Nat.pred (List.length p) > 0
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

  have g : Nat.pred (List.length p) < List.length p
  cases p with
  | nil =>
    simp at neq
  | cons hd tl =>
    simp
  specialize conn gt_zero g

  rw [get_a] at conn
  specialize h conn
  exact absurd reachCirc h

lemma acyclicIffAllNotReachedFromCycle (G: Graph A): isAcyclic G ↔ ∀ (a:A), a ∈ G.vertices → ¬ reachedFromCycle a G :=
by
  constructor
  intro acyclic
  intro a
  unfold reachedFromCycle
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
  have isLt: 0 < List.length c
  cases c with
  | nil =>
    simp at g
  | cons hd tl =>
    simp
  specialize h (List.get c (Fin.mk 0 isLt))
  unfold reachedFromCycle at h
  simp at h

  have get_c_mem: List.get c { val := 0, isLt := isLt } ∈ G.vertices
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
  have walk: isWalk [List.get c { val := 0, isLt := isLt }] G
  apply isWalkSingleton
  rcases cycle with ⟨walk_c,_⟩
  unfold isWalk at walk_c
  rcases walk_c with ⟨walk_c,_⟩
  apply walk_c
  apply List.get_mem

  specialize h walk
  simp[cycle] at h




lemma frontRepetitionInWalkImpliesCycle (a:A) (G:Graph A) (visited: List A) (walk: isWalk (a::visited) G) (mem: a ∈ visited): isCycle (a::(getSubListToMember visited a mem)) G :=
by
  unfold isCycle
  simp
  have h : ¬ Nat.succ (List.length (getSubListToMember visited a mem)) < 2
  push_neg
  cases h':getSubListToMember visited a mem with
  | nil =>
    have p: getSubListToMember visited a mem ≠ []
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
    have p: getSubListToMember visited a mem ≠ []
    apply getSubListToMemberNonEmpty
    exact absurd h' p
  | cons hd tl =>
    apply isWalk_extends_predecessors
    rw [← h']
    apply getSubListToMemberPreservesWalk (walk:= isWalk_of_cons walk)
    unfold isWalk at walk
    rcases walk with ⟨_, conn⟩
    specialize conn (Nat.succ 0)
    simp at conn
    have g : Nat.succ 0 < List.length (a :: visited)
    simp
    apply Nat.succ_lt_succ
    cases visited with
    | nil =>
      simp at mem
    | cons hd' tl' =>
      simp
    specialize conn g
    have isLt: 0 < List.length visited
    apply Nat.lt_of_succ_lt_succ
    apply g
    have first_vis: List.get visited { val := 0, isLt := isLt} = hd
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


def Lean.HashSet.Subset [Hashable B] (S S': HashSet B): Prop := ∀ (b:B), S.contains b → S'.contains b

instance [Hashable B]: HasSubset (HashSet B) := ⟨Lean.HashSet.Subset⟩

lemma Lean.HashSet.Subset.refl [Hashable B] {S1: HashSet B} : S1 ⊆ S1 :=
by
  unfold_projs at *
  unfold Subset at *
  simp


lemma Lean.HashSet.Subset.trans [Hashable B] {S1 S2 S3: HashSet B} (h1: S1 ⊆ S2) (h2: S2 ⊆ S3): S1 ⊆ S3 :=
by
  unfold_projs at *
  unfold Subset at *
  intro b S1_b
  apply h2
  apply h1
  apply S1_b

lemma Lean.HashSet.Subset.Iff [Hashable B] {S1 S2: HashSet B} : S1 ⊆ S2 ↔ ∀ (b:B), S1.contains b → S2.contains b :=
by
  unfold_projs
  unfold HashSet.Subset
  simp

lemma Lean.HashSet.contains_insert [Hashable B] {S1: HashSet B} (b:B ): ∀ (b':B), (S1.insert b).contains b' ↔ S1.contains b' ∨ b = b' :=
by
  intro b'
  unfold contains
  unfold insert
  cases S1 with
  | mk val prop =>
    simp
    unfold HashSetImp.insert
    cases val with
    | mk n buckets =>
      simp
      sorry



lemma Lean.HashSet.empty_contains [Hashable B]: ∀ (b:B), ¬ HashSet.empty.contains b :=
by
  intro b
  simp
  unfold contains
  unfold empty
  unfold mkHashSet
  simp
  unfold mkHashSetImp
  unfold HashSetImp.contains
  simp
  by_contra p
  rw [List.contains_eq_any_beq, Bool.not_eq_false, List.any_eq_true] at p
  simp at p
  rw [Array.getElem_eq_data_get] at p
  unfold mkArray at p
  simp only at p
  rw [List.get_replicate] at p
  simp at p



def foldl_except_set [Hashable B] (f: A → HashSet B → (Except String (HashSet B))) (l: List A) (init: HashSet B): Except String (HashSet B) :=
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
      have hd_mem: hd ∈ hd::tl
      simp
      apply subs init S' hd hd_mem h'
      apply ih S'
      intro T T' a' a_tl
      apply subs
      simp [a_tl]
      apply h

lemma foldl_except_set_contains_list_map [Hashable B] (f: A → HashSet B → (Except String (HashSet B))) (l: List A) (init: HashSet B) (subs: ∀ (S S':HashSet B ) (a:A), a ∈ l →  f a S = Except.ok S' → S ⊆ S')(map: A → B) (map_prop: ∀ (a:A) (S S':HashSet B ), f a S  = Except.ok S' →  S'.contains (map a) ) (T: HashSet B) (get_T: foldl_except_set f l init = Except.ok T) : ∀ (b:B), b ∈  (List.map map l) → T.contains b :=
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
      have subs':  ∀ (S S' : HashSet B) (a : A), a ∈ tl → f a S = Except.ok S' → S ⊆ S'
      intro S S' a a_tl f_a
      apply subs S S' a
      simp [a_tl]
      apply f_a
      cases b_mem with
      | inl b_hd =>
        have S_T: S ⊆ T
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
    constructor
    intro h a a_mem
    simp at a_mem
    rcases h with ⟨S, foldl⟩
    cases a_mem with
    | inl a_hd =>
      unfold foldl_except_set at foldl
      rw [a_hd]
      cases h: f hd init with
      | ok S' =>
        unfold Except.isOk
        unfold Except.toBool
        simp
      | error e =>
        simp [h] at foldl
    | inr a_tl =>
      unfold foldl_except_set at foldl
      cases h: f hd init with
      | ok S' =>
        specialize ih S'
        have S'_prop: ∀ (b : B), S'.contains b → p b
        apply f_prev hd init S' init_prop h
        specialize ih S'_prop
        simp [h] at foldl
        rw [← f_ignore_B a S' init S'_prop init_prop]
        revert a
        rw [← ih]
        use S
      | error e =>
        simp [h] at foldl

    intro h
    have f_hd_result: ∃ (S: HashSet B), f hd init = Except.ok S
    rw [except_is_ok_iff_exists]
    apply h
    simp
    unfold foldl_except_set
    rcases f_hd_result with ⟨S', f_S'⟩
    simp [f_S']
    specialize ih S'
    have S'_prop: ∀ (b:B), S'.contains b → p b
    apply f_prev hd init S' init_prop f_S'
    specialize ih S'_prop
    rw [ih]
    intro a a_mem
    rw [f_ignore_B a S' init S'_prop init_prop]
    apply h
    simp [a_mem]


def addElementIfOk [Hashable A] (e: Except String (HashSet A)) (a:A): Except String (HashSet A) :=
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


lemma canReachLemma (a:A) (G: Graph A) (mem: a ∈ G.vertices) (f: A → List A → Except String Unit): (∀ (b : A), canReach b a G → f b (Graph.predecessors G b) = Except.ok ()) ↔ (∀ (b: A), b ∈ G.predecessors a → (∀ (c : A), canReach c b G → f c (Graph.predecessors G c) = Except.ok ())) ∧ f a (G.predecessors a) = Except.ok () :=
by

  constructor
  intro h
  constructor
  intro b b_pred
  intro c reach_c
  apply h
  unfold canReach
  unfold canReach at reach_c
  rcases reach_c with ⟨p, neq, walk, get_c, get_b⟩
  use p++[a]
  have neq': p++[a] ≠ []
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
    apply b_pred
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
      rw [← get_b, get_a]
      apply And.right h
    | cons hd' tl' =>
      rcases h with ⟨left,_⟩
      have isLt: Nat.pred (Nat.pred (hd::hd'::tl').length) < (hd::hd'::tl').length
      simp
      apply Nat.lt_trans (m:= Nat.succ tl'.length)
      simp
      simp
      have pred: List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt) ∈ G.predecessors a
      rw [← get_a]
      unfold isWalk at walk
      rcases walk with ⟨_,conn⟩
      apply conn
      simp
      specialize left (List.get (hd::hd'::tl') (Fin.mk (Nat.pred (Nat.pred (hd::hd'::tl').length)) isLt)) pred
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

lemma allTrueIfAllCanReachTrue (f: A → List A → Except String Unit) (G: Graph A): (∀ (a:A), a ∈ G.vertices → f a (G.predecessors a) = Except.ok ()) ↔ ∀ (a:A), a ∈ G.vertices → ∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok () :=
by
  constructor
  intro h a _ b reach
  apply h
  unfold canReach at reach
  rcases reach with ⟨p, _, walk, get_b, _⟩
  apply isWalkImplSubset' walk
  rw [← get_b]
  apply List.get_mem

  intro h a a_mem
  apply h a a_mem
  apply canReach_refl
  apply a_mem

lemma not_mem_of_empty_intersection {l1 l2: List A} (inter: l1 ∩ l2 = ∅): ∀ (a:A), a ∈ l1 → ¬ a ∈ l2 :=
by
  intro a a_l1
  by_contra a_l2
  have h: a ∈ l1 ∧ a ∈ l2
  apply And.intro a_l1 a_l2
  rw [← List.mem_inter_iff] at h
  rw [inter] at h
  simp at h

def dfs_step [Hashable A] (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List A) (walk: isWalk (a::currWalk) G) (not_mem: ¬ (a ∈ currWalk))(visited: HashSet A) : Except String (HashSet A) :=
  if visited.contains a
  then Except.ok visited
  else
    match f a (G.predecessors a) with
    | Except.error msg => Except.error msg
    | Except.ok _ =>
      if pred_walk: (G.predecessors a) ∩ (a::currWalk) = []
      then

      addElementIfOk (foldl_except_set (fun ⟨x, _h⟩ S =>
        dfs_step x G f (a::currWalk) (isWalk_extends_predecessors walk x _h) (not_mem_of_empty_intersection pred_walk x _h) S) (G.predecessors a).attach visited) a
      else
        Except.error "Cycle detected"
termination_by dfs_step node G f currWalk walk not_mem visited => Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)
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
    have mem_walk: a ∈ a::currWalk
    simp
    apply isWalkImplSubset' walk a mem_walk
    apply not_mem
  | inr h =>
    rcases h with ⟨left,right⟩
    push_neg at right
    simp [left,right]



lemma dfs_step_subset [Hashable A] (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List A) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet A): ∀ (S:HashSet A), dfs_step a G f currWalk walk not_mem visited = Except.ok S → visited ⊆ S :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)  with n ih generalizing a currWalk visited

  --base case: impossible as a is not in walk and yet everything must be in the walk
  rw[Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices
  apply isWalkImplSubset' walk
  simp
  specialize h a_G
  exact absurd h not_mem

  intro S get_S
  have a_mem: a ∈ G.vertices
  apply isWalkImplSubset' walk
  simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) = n
  rw [Nat.succ_eq_add_one] at h
  have h': List.toFinset G.vertices \ List.toFinset currWalk = insert a (List.toFinset G.vertices \ List.toFinset (a :: currWalk))
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
  cases f_a: f a (Graph.predecessors G a) with
  | error e=>
    simp[f_a] at get_S
  | ok _ =>
    simp [f_a] at get_S
    have int_walk_pred: Graph.predecessors G a ∩ (a :: currWalk) = []
    by_contra p
    simp [p] at get_S
    simp [int_walk_pred] at get_S
    rw [addElementIfOk_exists_ok'] at get_S
    rcases get_S with ⟨S', S_S', foldl_result⟩
    rw [S_S']
    have visit_S': visited ⊆ S'
    apply foldl_except_set_subset (l:=(G.predecessors a).attach) (get_S:= foldl_result)
    simp
    intro T T' x x_pred
    apply ih
    apply card
    -- end have visit_S'
    rw [HashSet.Subset.Iff]
    intro x x_vis
    rw [HashSet.contains_insert]
    left
    rw [HashSet.Subset.Iff] at visit_S'
    apply visit_S' x x_vis

lemma dfs_step_returns_root_element [Hashable A] (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List A) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet A) (S:HashSet A) (get_S:dfs_step a G f currWalk walk not_mem visited = Except.ok S): S.contains a :=
by
  unfold dfs_step at get_S
  by_cases a_visit: visited.contains a
  simp [a_visit] at get_S
  rw [get_S] at a_visit
  apply a_visit

  simp [a_visit] at get_S
  cases f_a: f a (Graph.predecessors G a) with
  | error e=>
    simp[f_a] at get_S
  | ok _ =>
    simp[f_a] at get_S
    by_cases h : Graph.predecessors G a ∩ (a :: currWalk) = []
    simp [h] at get_S
    rw [addElementIfOk_exists_ok'] at get_S
    rcases get_S with ⟨S', S_S',_⟩
    rw [S_S']
    rw [HashSet.contains_insert]
    right
    rfl

    simp [h] at get_S

lemma dfs_step_preserves_notReachedFromCycleAndCounterExample [Hashable A] (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List A) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet A) (visited_prop: ∀ (a:A), visited.contains a → ¬ reachedFromCycle a G ∧ ∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok ()) (S: HashSet A) (get_S: dfs_step a G f currWalk walk not_mem visited = Except.ok S): ∀ (a:A),  S.contains a → ¬ reachedFromCycle a G ∧ ∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok () :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)  with n ih generalizing a currWalk visited S

  --base case: impossible as a is not in walk and yet everything must be in the walk
  rw[Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices
  apply isWalkImplSubset' walk
  simp
  specialize h a_G
  exact absurd h not_mem

  --step
  have a_mem: a ∈ G.vertices
  apply isWalkImplSubset' walk
  simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) = n
  rw [Nat.succ_eq_add_one] at h
  have h': List.toFinset G.vertices \ List.toFinset currWalk = insert a (List.toFinset G.vertices \ List.toFinset (a :: currWalk))
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
  cases f_a: f a (Graph.predecessors G a) with
  | error e =>
    simp [f_a] at get_S
  | ok _ =>
    simp [f_a] at get_S
    have inter: Graph.predecessors G a ∩ (a :: currWalk) = []
    by_contra p
    simp [p] at get_S
    simp [inter] at get_S
    rw [addElementIfOk_exists_ok'] at get_S
    rcases get_S with ⟨S', S_S', foldl_result⟩
    have preserve_S': ∀ (a : A), S'.contains a → ¬reachedFromCycle a G ∧ ∀ (b : A), canReach b a G → f b (Graph.predecessors G b) = Except.ok ()
    apply foldl_except_set_preserves_p (init_prop:=visited_prop) (h:= foldl_result)
    simp
    intro b b_pred T T' T_prop dfs_T'
    specialize ih b (a::currWalk) (isWalk_extends_predecessors walk b b_pred) (not_mem_of_empty_intersection inter b b_pred) T T_prop T' dfs_T' card
    apply ih
    -- end preserve_S'

    --split cases
    intro b
    rw [S_S']
    intro b_mem
    rw [HashSet.contains_insert] at b_mem
    cases b_mem with
    | inl b_S' =>
      apply preserve_S' b b_S'
    | inr b_a =>
      have b_mem: b ∈ G.vertices
      rw [← b_a]
      apply a_mem
      rw [NotreachedFromCycleIffPredecessorsNotReachedFromCycle (mem:=b_mem), canReachLemma (mem:=b_mem)]
      simp [← b_a, f_a]
      rw [← forall_and]
      intro a'
      rw [← imp_and]
      intro a'_pred
      apply preserve_S'
      apply foldl_except_set_contains_list_map (get_T:=foldl_result) (map:= fun ⟨x,_h⟩ => x)
      simp
      intro T T' x x_pred
      apply dfs_step_subset

      simp
      intro x x_pred
      apply dfs_step_returns_root_element

      simp
      apply a'_pred



lemma dfs_step_sematics [Hashable A] (a: A) (G: Graph A) (f: A → List A → Except String Unit) (currWalk: List A) (walk: isWalk (a::currWalk) G) (not_mem: ¬ a ∈ currWalk) (visited: HashSet A) (visited_prop: ∀ (a:A), visited.contains a → ¬ reachedFromCycle a G ∧ ∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok ()):  Except.isOk (dfs_step a G f currWalk walk not_mem visited) ↔  ¬ reachedFromCycle a G ∧ (∀ (b:A), canReach b a G → f b (G.predecessors b) = Except.ok ()) :=
by
  induction' h:Finset.card (List.toFinset G.vertices \ List.toFinset currWalk)  with n ih generalizing a currWalk visited

  --base case: impossible as a is not in walk and yet everything must be in the walk
  rw[Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff] at h
  simp at h
  have a_G: a ∈ G.vertices
  apply isWalkImplSubset' walk
  simp
  specialize h a_G
  exact absurd h not_mem

  --step
  have a_mem: a ∈ G.vertices
  apply isWalkImplSubset' walk
  simp
  have card: Finset.card (List.toFinset G.vertices \ List.toFinset (a :: currWalk)) = n
  rw [Nat.succ_eq_add_one] at h
  have h': List.toFinset G.vertices \ List.toFinset currWalk = insert a (List.toFinset G.vertices \ List.toFinset (a :: currWalk))
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
  apply dfs_step_preserves_notReachedFromCycleAndCounterExample (visited_prop:=visited_prop)
  apply dfs_get
  apply dfs_step_returns_root_element (get_S:=dfs_get)

  intro h'
  unfold dfs_step
  by_cases a_visit: visited.contains a
  simp [a_visit]
  apply except_is_ok_of_ok

  simp[a_visit]
  rcases h' with ⟨reach_cycle, reach_f⟩
  have f_a: f a (G.predecessors a) = Except.ok ()
  apply reach_f
  apply canReach_refl a G a_mem
  simp [f_a]

  have pred_walk: Graph.predecessors G a ∩ (a :: currWalk) = []
  cases inter: Graph.predecessors G a ∩ (a :: currWalk) with
  | nil =>
    simp
  | cons hd tl =>
    have hd_mem: hd ∈ G.predecessors a ∧ hd ∈ (a::currWalk)
    rw [← List.mem_inter_iff, inter]
    simp
    rcases hd_mem with ⟨hd_pred, hd_a_currWalk⟩

    have cycle_hd: isCycle (hd::(getSubListToMember (a::currWalk) hd hd_a_currWalk)) G
    apply frontRepetitionInWalkImpliesCycle
    apply isWalk_extends_predecessors walk hd hd_pred

    have reachedFromCycleHd: reachedFromCycle hd G
    unfold reachedFromCycle
    use hd::(getSubListToMember (a::currWalk) hd hd_a_currWalk)
    constructor
    apply cycle_hd
    use hd
    simp
    apply canReach_refl
    apply G.complete
    apply a_mem
    apply hd_pred

    rw [NotreachedFromCycleIffPredecessorsNotReachedFromCycle (mem:= a_mem)] at reach_cycle
    specialize reach_cycle hd hd_pred
    exact absurd reachedFromCycleHd reach_cycle

  simp [pred_walk]
  rw [← except_is_ok_iff_exists, addElementIfOk_exists_ok,foldl_except_set_is_ok (init_prop:=visited_prop)]
  simp
  intro b b_pred
  have b_mem: b ∈ G.vertices
  apply G.complete a a_mem b b_pred
  specialize ih b (a::currWalk) (isWalk_extends_predecessors walk b b_pred) (not_mem_of_empty_intersection pred_walk b b_pred) visited visited_prop card
  rw [ih]
  constructor
  rw [NotreachedFromCycleIffPredecessorsNotReachedFromCycle (mem:= a_mem)] at reach_cycle
  apply reach_cycle b b_pred
  rw [canReachLemma (mem:=a_mem)] at reach_f
  apply And.left (reach_f )
  apply b_pred

  simp
  intro b b_pred S S' S_prop S'_prop
  rw [ih, ih]
  apply S'_prop
  apply card
  apply S_prop
  apply card

  simp
  intro b b_pred S S' S_prop
  apply dfs_step_preserves_notReachedFromCycleAndCounterExample
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

def dfs [Hashable A] (G: Graph A) (f: A → List A → Except String Unit) : Except String Unit :=
  isOkOrMessage (foldl_except_set (fun ⟨x,_h⟩ S => dfs_step x G f [] (isWalkSingleton G x _h) (List.not_mem_nil x) S) G.vertices.attach HashSet.empty )

lemma dfs_semantics [Hashable A] (G: Graph A) (f: A → List A → Except String Unit): dfs G f = Except.ok () ↔ isAcyclic G ∧ ∀ (a:A), a ∈ G.vertices → f a (G.predecessors a) = Except.ok () :=
by
  unfold dfs
  rw [isOkOrMessageOkIffExceptionIsOk, acyclicIffAllNotReachedFromCycle, allTrueIfAllCanReachTrue]
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


  use (fun x => ¬reachedFromCycle x G ∧ ∀ (b : A), canReach b x G → f b (Graph.predecessors G b) = Except.ok ())
  simp [HashSet.empty_contains]

  simp
  intro a a_mem S S' S_prop S'_prop
  rw [dfs_step_sematics (visited_prop:=S_prop), dfs_step_sematics (visited_prop:=S'_prop)]

  simp
  intro a _pred S S' S_prop get_S'
  apply dfs_step_preserves_notReachedFromCycleAndCounterExample (visited_prop:=S_prop)
  apply get_S'


def extractTree {A: Type} [DecidableEq A] (a:A) (G: Graph A) (mem: a ∈ G.vertices) (acyclic: isAcyclic G): tree A :=
  tree.node a (List.map (fun ⟨x, _h⟩ => extractTree x G (G.complete a mem x _h) acyclic) (G.predecessors a).attach)
termination_by extractTree a G mem acyclic => Finset.card (globalPredecessors a G)
decreasing_by
  simp_wf
  apply Finset.card_lt_card
  apply globalPredecessorsSSubsetWhenAcyclicAndPredecessor
  apply acyclic
  apply _h
  apply mem


lemma rootOfExtractTree (a:A) (G: Graph A) (mem: a ∈ G.vertices) (acyclic: isAcyclic G): root (extractTree a G mem acyclic ) = a :=
by
  unfold extractTree
  unfold root
  simp

variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def locallyValid (P: program τ) (d: database τ) (v: groundAtom τ) (G: Graph (groundAtom τ)): Prop :=
 (∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding r g = groundRuleFromAtoms v (G.predecessors v) ) ∨ ((G.predecessors v) = [] ∧ d.contains v)

def locallyValidityChecker (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (l: List (groundAtom τ)) (a: groundAtom τ)(ruleToString: rule τ → String): Except String Unit :=
  if l.isEmpty
  then
    if d.contains a
    then Except.ok ()
    else checkRuleMatch m (groundRule.mk a l) ruleToString
  else
    checkRuleMatch m (groundRule.mk a l) ruleToString

lemma locallyValidityCheckerUnitIffLocallyValid (P: List (rule τ)) (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (G: Graph (groundAtom τ)) (a: groundAtom τ) (l: List (groundAtom τ)) (l_prop: l = G.predecessors a) (ruleToString: rule τ → String) (ssm: m = parseProgramToSymbolSequenceMap P (fun _ => [])):  locallyValidityChecker m d l a ruleToString = Except.ok () ↔ locallyValid P.toFinset d a G :=
by
  unfold locallyValid
  unfold locallyValidityChecker
  rw [l_prop]
  simp
  constructor

  intro h
  by_cases empty: List.isEmpty (G.predecessors a) = true
  simp [empty] at h
  by_cases db: d.contains a
  right
  constructor
  rw [List.isEmpty_iff_eq_nil] at empty
  apply empty
  apply db
  simp at db
  specialize h db
  rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)] at h
  left
  simp at h
  apply h

  simp [empty] at h
  rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)] at h
  left
  simp at h
  apply h

  intro h
  by_cases empty: List.isEmpty (Graph.predecessors G a)
  rw [if_pos empty]
  by_cases db: d.contains a
  simp [db]
  simp [db]
  cases h with
  | inl ruleCase =>
    rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)]
    simp
    apply ruleCase
  | inr dbCase =>
    rcases dbCase with ⟨_, n_db⟩
    exact absurd n_db db
  simp [empty]
  cases h with
  | inl ruleCase =>
    rw [checkRuleMatchOkIffExistsRuleForGroundRule (P:= P) (ssm:= ssm)]
    simp
    apply ruleCase
  | inr dbCase =>
    rcases dbCase with ⟨n_empty, _⟩
    rw [← List.isEmpty_iff_eq_nil] at n_empty
    exact absurd n_empty empty



lemma extractTreeStepValidProofTreeIffAllLocallyValidAndAcyclic (P: program τ) (d: database τ) (a: groundAtom τ) (G: Graph (groundAtom τ)) (acyclic: isAcyclic G) (mem: a ∈ G.vertices) (valid: ∀ (a: groundAtom τ), a ∈ G.vertices → locallyValid P d a G): isValid P d (extractTree a G mem acyclic) :=
by
  induction' h:(height (extractTree a G mem acyclic)) using Nat.strongInductionOn with n ih generalizing a
  have valid_a: locallyValid P d a G
  apply valid a mem
  unfold locallyValid at valid_a
  cases valid_a with
  | inl ruleCase =>
    rcases ruleCase with ⟨r,g,rP, grounding_r⟩
    unfold extractTree
    unfold isValid
    left
    use r
    use g
    constructor
    apply rP
    constructor
    simp
    rw [grounding_r, groundRuleEquality]
    unfold groundRuleFromAtoms
    simp
    apply List.ext_get
    rw [List.length_map, List.length_attach]
    intro n h1 h2
    simp
    rw [rootOfExtractTree]
    rw [List.all₂_iff_forall]
    simp
    intro t x x_pred extract
    specialize ih (height t)
    have height_t_n: height t < n
    rw [← h]
    apply heightOfMemberIsSmaller
    unfold member
    unfold extractTree
    simp
    use x
    use x_pred

    specialize ih height_t_n x (G.complete a mem x x_pred)
    rw [extract] at ih
    simp at ih
    apply ih
  | inr dbCase =>
    unfold extractTree
    unfold isValid
    right
    simp
    apply dbCase

lemma verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (P: program τ) (d: database τ)  (G: Graph (groundAtom τ)) (acyclic: isAcyclic G)  (valid: ∀ (a: groundAtom τ), a ∈ G.vertices → locallyValid P d a G): List.toSet G.vertices ⊆ proofTheoreticSemantics P d :=
by
  rw [Set.subset_def]
  intro a a_mem
  rw [← List.toSet_mem] at a_mem
  unfold proofTheoreticSemantics
  simp
  use extractTree a G a_mem acyclic
  constructor
  apply rootOfExtractTree
  apply extractTreeStepValidProofTreeIffAllLocallyValidAndAcyclic
  apply valid
