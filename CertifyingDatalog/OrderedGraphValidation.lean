import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation


abbrev orderedProofGraph (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]:= Array ((groundAtom τ) × List ℕ)

variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

def labels (proof:orderedProofGraph τ): List (groundAtom τ):= (Array.map Prod.fst proof).toList

lemma labelsMemIffExistsPos (proof:orderedProofGraph τ) (ga: groundAtom τ): ga ∈ labels proof ↔ ∃ (i: ℕ) (h: i < proof.size), Prod.fst (proof[i]) = ga := by
  unfold labels
  rw [Array.toList_eq, ← Array.mem_def, Array.mem_iff_get]
  simp


def orderedProofGraph.locallyValid (proof: orderedProofGraph τ) (P: program τ) (d: database τ) (i: ℕ) (hi: i < proof.size):=
  ∃ (h: ∀ (j: ℕ), j ∈ (Prod.snd proof[i]) → j < i),
    (Prod.snd proof[i] = [] ∧ d.contains (Prod.fst proof[i]) )
    ∨ (∃(r: rule τ) (g:grounding τ),
      r ∈ P ∧
      ruleGrounding r g =
      {head:= Prod.fst proof[i], body:=
      List.map (fun ⟨x, _h⟩ => Prod.fst (Array.get proof (Fin.mk x (Nat.lt_trans (h x _h) hi)))) (Prod.snd proof[i]).attach})

def orderedProofGraph.isValid (proof: orderedProofGraph τ) (P: program τ) (d: database τ): Prop :=
  ∀ (i: ℕ) (hi: i < proof.size), locallyValid proof P d i hi

lemma isValidSafeAccessSuccessors {proof: orderedProofGraph τ} {P: program τ} {d: database τ} (valid: orderedProofGraph.isValid proof P d) (i: ℕ) (hi: i < proof.size): ∀ (j: ℕ), j ∈ Prod.snd proof[i] → j < proof.size := by
  simp [orderedProofGraph.isValid, orderedProofGraph.locallyValid] at valid
  intro j j_mem
  specialize valid i hi
  rcases valid with ⟨h,_⟩
  apply Nat.lt_trans _ hi
  exact h j j_mem

def checkListSmallerElement (element: ℕ) (l: List ℕ): Except String Unit :=
  match l with
  | [] => Except.ok ()
  | hd::tl => if hd < element
              then checkListSmallerElement element tl
              else Except.error "Graph not ordered"

lemma checkListSmallerElementIff (element: ℕ) (l: List ℕ): checkListSmallerElement element l = Except.ok () ↔ ∀ (j: ℕ), j ∈ l → j < element := by
  induction l with
  | nil =>
    simp [checkListSmallerElement]
  | cons hd tl ih =>
    simp [checkListSmallerElement]
    split; simp[*];simp[*]




def validatePosition (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (proof: orderedProofGraph τ) (pos: ℕ) (posValid: pos < proof.size): Except String Unit :=
  let successors := Prod.snd proof[pos]
  match h:checkListSmallerElement pos successors with
  | Except.error e => Except.error e
  | Except.ok _ =>
    have hsucc: ∀ (j: ℕ), j ∈ successors → j < pos := by rw [checkListSmallerElementIff] at h; exact h

    if successors.isEmpty
    then
      if d.contains (Prod.fst proof[pos]) = true
      then Except.ok ()
      else checkRuleMatch m {head:= Prod.fst proof[pos], body := []}
    else
      checkRuleMatch m {head:= Prod.fst proof[pos], body:= List.map (fun ⟨x,_h⟩ => Prod.fst (proof.get (Fin.mk x (Nat.lt_trans (hsucc x _h) posValid)))) successors.attach}


lemma validatePositionOkIffLocallyValid (P: List (rule τ)) (d: database τ) (proof: orderedProofGraph τ) (pos: ℕ) (posValid: pos < proof.size):
  validatePosition (parseProgramToSymbolSequenceMap P (fun _ => [])) d proof pos posValid = Except.ok () ↔
 orderedProofGraph.locallyValid  proof P.toFinset d pos posValid := by
  simp[orderedProofGraph.locallyValid, validatePosition]
  split
  · simp
    rename_i s checkList
    have checkList': ¬ checkListSmallerElement pos proof[pos].2 = Except.ok () := by
      simp[checkList]
    simp [checkListSmallerElementIff] at checkList'
    intro h
    rcases checkList' with ⟨i, i_mem,i_le⟩
    specialize h i i_mem
    rw [← not_le] at h
    contradiction


  · rename_i hsuccs
    rw [checkListSmallerElementIff] at hsuccs
    split
    · rename_i succEmpty
      split
      · rename_i db_contains
        simp
        use hsuccs
        left
        simp [← List.isEmpty_iff_eq_nil, succEmpty, db_contains]
      · rename_i db_contains
        simp [db_contains, checkRuleMatchOkIffExistsRuleForGroundRule]
        rw [List.isEmpty_iff_eq_nil] at succEmpty
        have h: List.attach proof[pos].2 = [] := by
            simp [succEmpty]
        rw [h]
        simp
        intro _ _ _ _
        exact hsuccs

    · rename_i succEmpty
      rw [List.isEmpty_iff_eq_nil] at succEmpty
      simp [succEmpty, checkRuleMatchOkIffExistsRuleForGroundRule]
      aesop



def validateOrderedProof.go (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (proof: orderedProofGraph τ) (pos: ℕ): Except String Unit :=
  if h: pos < proof.size
  then
    match validatePosition m d proof pos h with
    | Except.error e => Except.error e
    | Except.ok _ => validateOrderedProof.go m d proof (Nat.succ pos)
  else
    Except.ok ()
termination_by proof.size - pos


lemma validateOrderedProofGoSemantics (P: List (rule τ)) (d: database τ) (proof: orderedProofGraph τ) (pos: ℕ):
validateOrderedProof.go (parseProgramToSymbolSequenceMap P (fun _ => [])) d proof pos = Except.ok () ↔
∀ (i: ℕ) (h: i < proof.size), pos ≤ i → orderedProofGraph.locallyValid  proof P.toFinset d i h := by
  induction' h': (proof.size -pos) with n ih generalizing pos
  · rw [Nat.sub_eq_zero_iff_le, ← not_lt] at h'
    unfold validateOrderedProof.go
    simp[h']
    intro i i_size pos_i
    exfalso
    simp at h'
    have size_i: proof.size ≤ i := Nat.le_trans h' pos_i
    rw [← not_lt] at size_i
    contradiction
  · constructor
    · intro h i i_size pos_i
      rw [le_iff_lt_or_eq] at pos_i
      unfold validateOrderedProof.go at h
      have pos_size: pos < proof.size := by
        cases pos_i with
        | inl pos_i => exact Nat.lt_trans pos_i i_size
        | inr pos_i => rw [pos_i]; exact i_size
      simp [pos_size] at h
      split at h
      · simp at h
      · rename_i validatePos
        rw [validatePositionOkIffLocallyValid] at validatePos
        cases pos_i with
        | inl pos_i =>
          have size_pos: Array.size proof - Nat.succ pos = n := by
            rw [Nat.sub_succ, h', Nat.pred_succ]
          specialize ih (Nat.succ pos) size_pos
          rw [ih] at h
          apply h
          apply Nat.succ_le_of_lt
          exact pos_i
        | inr pos_i =>
          simp_rw [← pos_i]
          exact validatePos
    · intro h
      unfold validateOrderedProof.go
      split
      · rename_i pos_size
        split
        · rename_i s validatePos
          have validatePos': ¬ validatePosition (parseProgramToSymbolSequenceMap P fun _ => []) d proof pos pos_size = Except.ok () := by simp [validatePos]
          rw [validatePositionOkIffLocallyValid] at validatePos'
          specialize h pos pos_size
          simp at h
          contradiction
        · have size_pos: Array.size proof - Nat.succ pos = n := by
            rw [Nat.sub_succ, h', Nat.pred_succ]
          specialize ih (Nat.succ pos) size_pos
          rw [ih]
          intro i i_proof pos_i
          apply h
          rw [Nat.succ_le] at pos_i
          apply Nat.le_of_lt pos_i
      · rfl



def validateOrderedProof (m: List τ.relationSymbols → List (rule τ)) (d: database τ) (proof: orderedProofGraph τ): Except String Unit := validateOrderedProof.go m d proof 0

lemma validateOrderedProofSemantics(P: List (rule τ)) (d: database τ) (proof: orderedProofGraph τ):
validateOrderedProof (parseProgramToSymbolSequenceMap P (fun _ => [])) d proof = Except.ok () ↔ orderedProofGraph.isValid proof P.toFinset d := by
  simp [validateOrderedProof, orderedProofGraph.isValid, validateOrderedProofGoSemantics]

def extractProofTree (proof: orderedProofGraph τ) {P: program τ} {d: database τ} (valid: orderedProofGraph.isValid proof P d) (pos: ℕ) (posValid: pos < proof.size): proofTree τ :=
  tree.node proof[pos].1 (List.map (fun ⟨x, _h⟩ => extractProofTree proof valid x (isValidSafeAccessSuccessors valid pos posValid x _h)) proof[pos].2.attach)
termination_by pos
decreasing_by
  simp_wf
  simp [orderedProofGraph.isValid, orderedProofGraph.locallyValid] at valid
  specialize valid pos posValid
  rcases valid with ⟨h,_⟩
  exact h x _h

lemma extractProofTreeRoot (proof: orderedProofGraph τ) {P: program τ} {d: database τ} (valid: orderedProofGraph.isValid proof P d) (pos: ℕ) (posValid: pos < proof.size):  root (extractProofTree proof valid pos posValid) = proof[pos].1 := by
  unfold extractProofTree
  unfold root
  simp

lemma extractProofTreeIsValid (proof: orderedProofGraph τ) {P: program τ} {d: database τ} (valid: orderedProofGraph.isValid proof P d) (pos: ℕ) (posValid: pos < proof.size): isValid P d (extractProofTree proof valid pos posValid) := by
  induction' pos using Nat.strongInductionOn with pos ih
  simp [orderedProofGraph.isValid, orderedProofGraph.locallyValid] at valid
  specialize valid pos posValid
  rcases valid with ⟨h, h'⟩
  cases h' with
  | inl h' =>
    unfold extractProofTree
    rcases h' with ⟨succEmpty, dbContain⟩
    have attachEmpty: List.attach proof[pos].2 = [] := by
      simp [succEmpty]
    simp [attachEmpty]
    unfold isValid
    right
    simp [dbContain]
  | inr h' =>
    unfold extractProofTree
    unfold isValid
    left
    rcases h' with ⟨r, rP, g, ground⟩
    use r
    use g
    simp [rP]
    constructor
    · rw [ground, groundRuleEquality]
      constructor
      · simp
      · apply List.ext_get
        simp

        intro n h1 h2
        simp
        rw [extractProofTreeRoot]
    · rw [List.forall_iff_forall_mem]
      simp
      intro t x x_mem ht
      rw [← ht]
      apply ih
      apply h
      exact x_mem

theorem validateOrderedProofIffValidAndSubset (P: List (rule τ)) (d: database τ) (proof: orderedProofGraph τ):
validateOrderedProof (parseProgramToSymbolSequenceMap P (fun _ => [])) d proof = Except.ok () ↔ orderedProofGraph.isValid proof P.toFinset d ∧ (labels proof).toSet ⊆ proofTheoreticSemantics P.toFinset d := by
  constructor
  intro h
  rw [validateOrderedProofSemantics] at h
  simp [h]
  simp [proofTheoreticSemantics, Set.subset_def, ← List.toSet_mem]
  intro ga ga_mem
  rw [labelsMemIffExistsPos] at ga_mem
  rcases ga_mem with ⟨pos, pos_valid, get_pos⟩
  use extractProofTree proof h pos pos_valid
  constructor
  · simp [extractProofTreeRoot, get_pos]
  · apply extractProofTreeIsValid

  intro h
  rcases h with ⟨h, _⟩
  rw [validateOrderedProofSemantics]
  exact h
