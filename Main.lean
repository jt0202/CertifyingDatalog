import «CertifyingDatalog»

def mergeList {A: Type} [DecidableEq A] (l1 l2: List A): List A :=
  match l1 with
  | [] => l2
  | hd::tl => if hd ∈ l2
              then mergeList tl l2
              else mergeList tl (hd::l2)

lemma mergeList_mem {A: Type} [DecidableEq A] (l1 l2: List A) (a:A): a ∈ mergeList l1 l2 ↔ a ∈ l1 ∨ a ∈ l2 :=
by
  induction l1 generalizing l2 with
  | nil =>
    unfold mergeList
    simp
  | cons hd tl ih =>
    unfold mergeList
    by_cases hd_l2: hd ∈ l2
    simp[hd_l2]
    rw [ih]
    constructor
    intro h
    cases h with
    | inl h =>
      left
      right
      apply h
    | inr h =>
      right
      apply h

    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        rw [← h] at hd_l2
        right
        apply hd_l2
      | inr h =>
        left
        apply h
    | inr h =>
      right
      apply h

    simp [hd_l2]
    rw [ih]
    simp
    tauto


def collectModel {helper: parsingArityHelper} (l: List (proofTree (parsingSignature helper))): List (groundAtom (parsingSignature helper)):=
  match l with
  | [] => []
  | hd::tl =>
    mergeList (proofTreeElements hd) (collectModel tl)

lemma collectModelHasTreeElements {helper: parsingArityHelper} (l: List (proofTree (parsingSignature helper))) (ga: groundAtom (parsingSignature helper)): ga ∈ collectModel l ↔ ∃ (t: proofTree (parsingSignature helper)), t ∈ l ∧ elementMember ga t = true := by
  induction l with
  | nil =>
    unfold collectModel
    simp
  | cons hd tl ih =>
    unfold collectModel
    rw [mergeList_mem, ih]
    simp
    rw [inProofTreeElementsIffelementMember]

lemma collectModelToSetIsSetOfValidTreesElements {helper: parsingArityHelper} (l: List (proofTree (parsingSignature helper))): List.toSet (collectModel l) = {ga: groundAtom (parsingSignature helper) | ∃ (t: proofTree (parsingSignature helper)), t ∈ l ∧ elementMember ga t = true} :=
by
  apply Set.ext
  intro ga
  rw [← List.toSet_mem, collectModelHasTreeElements]
  simp



def checkValidnessMockDatabase {helper: parsingArityHelper} (problem: verificationProblem helper): Except String Unit :=
  let d:= mockDatabase (parsingSignature helper)
  match validateTreeList problem.program d problem.trees with
  | Except.error e => Except.error e
  | Except.ok _ => Except.ok ()

lemma checkValidnessMockDatabaseUnitIffAllTreesAreValid {helper: parsingArityHelper}  (problem: verificationProblem helper): checkValidnessMockDatabase problem = Except.ok () ↔ ∀ (t: proofTree (parsingSignature helper)), t ∈ problem.trees → isValid (List.toFinset problem.program) (mockDatabase (parsingSignature helper)) t :=
by
  unfold checkValidnessMockDatabase
  simp
  rw [← validateTreeListUnitIffAllTreesValid]
  cases validateTreeList problem.program (mockDatabase (parsingSignature helper)) problem.trees with
  | error e =>
    simp
  | ok u =>
    simp

def checkValidnessGraphMockDatabase {helper: parsingArityHelper} (problem: graphVerificationProblem helper):  Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap problem.program (fun _ => [])
  let d:= mockDatabase (parsingSignature helper)
  dfs problem.graph (fun a l => localValidityCheck m d l a)

lemma checkValidnessGraphMockDatabaseIffAllValid {helper: parsingArityHelper}  (problem: graphVerificationProblem helper): checkValidnessGraphMockDatabase problem = Except.ok () ↔ isAcyclic problem.graph ∧ (∀ (a:ℕ) (mem: a ∈ problem.graph.vertices), locallyValid problem.program.toFinset (mockDatabase (parsingSignature helper)) a problem.graph mem)  ∧ problem.graph.labels.toSet ⊆ proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) :=
by
  unfold checkValidnessGraphMockDatabase
  rw [dfs_semantics]
  constructor
  intro h
  rcases h with ⟨acyc, localValid⟩
  constructor
  apply acyc
  constructor
  intro a a_mem
  specialize localValid a a_mem
  rw [localValidityCheckUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at localValid
  apply localValid
  rfl
  apply verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (acyclic:=acyc)
  intro a a_mem
  specialize localValid a a_mem
  rw [localValidityCheckUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at localValid
  apply localValid
  rfl

  intro h
  rcases h with ⟨acyclic, valid, _ ⟩
  constructor
  apply acyclic
  intro a a_mem
  rw [localValidityCheckUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)]
  apply valid a a_mem
  rfl



def mainCheckMockDatabase {helper: parsingArityHelper} (problem: verificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): Except String Unit :=
  let d:= mockDatabase (parsingSignature helper)
  let model:= collectModel problem.trees
  match validateTreeList problem.program d problem.trees with
  | Except.error e => Except.error e
  | Except.ok _ =>
    match modelChecker model problem.program safe with
    | Except.error e => Except.error e
    | Except.ok _ =>
      if mockDatabaseContainedInModel d (List.toSet model) = true
      then Except.ok ()
      else Except.error "Model does not contain database"

lemma mainCheckMockDatabaseUnitIffSolution {helper: parsingArityHelper}  (problem: verificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): mainCheckMockDatabase problem safe = Except.ok () ↔ (List.toSet (collectModel problem.trees)) = proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) ∧ ∀ (t: proofTree (parsingSignature helper)), t ∈ problem.trees → isValid problem.program.toFinset (mockDatabase (parsingSignature helper)) t:= by
  constructor
  unfold mainCheckMockDatabase
  simp
  intro h

  cases valid_trees: validateTreeList problem.program (mockDatabase (parsingSignature helper)) problem.trees with
  | error e => simp [valid_trees] at h
  | ok _ =>
    simp [valid_trees] at h
    cases model: modelChecker (collectModel problem.trees) problem.program safe with
    | error e => simp[model] at h
    | ok _ =>
      simp [model] at h
      rw [validateTreeListUnitIffSubsetSemanticsAndAllValid] at valid_trees
      rcases valid_trees with ⟨left,right⟩
      rw [modelCheckerUnitIffAllRulesTrue] at model
      constructor
      apply Set.Subset.antisymm
      rw [collectModelToSetIsSetOfValidTreesElements]
      apply left
      rw [SemanticsEquivalence]
      apply leastModel
      unfold model
      constructor
      apply model
      rw [← mockDatabaseContainedInModelTrue]
      have db: mockDatabaseContainedInModel (mockDatabase (parsingSignature helper)) (List.toSet (collectModel problem.trees)) = true := by
        by_contra p
        simp at p
        rw [p] at h
        simp at h

      apply db
      apply right

  intro h
  rcases h with ⟨sol_eq, valid_tree⟩
  unfold mainCheckMockDatabase
  simp
  have p: validateTreeList problem.program (mockDatabase (parsingSignature helper)) problem.trees = Except.ok () := by
    rw [validateTreeListUnitIffSubsetSemanticsAndAllValid]
    constructor
    rw [← collectModelToSetIsSetOfValidTreesElements]
    rw [sol_eq]
    apply valid_tree

  simp [p]
  have model: model (List.toFinset problem.program) (mockDatabase (parsingSignature helper)) (List.toSet (collectModel problem.trees)) := by
    rw [sol_eq]
    apply proofTheoreticSemanticsIsModel
  unfold model at model
  rcases model with ⟨model,_⟩

  have q: modelChecker (collectModel problem.trees) problem.program safe = Except.ok () := by
    rw [modelCheckerUnitIffAllRulesTrue]
    apply model

  simp[q]
  unfold mockDatabaseContainedInModel
  simp


def mainCheckGraphMockDatabase {helper: parsingArityHelper} (problem: graphVerificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap problem.program (fun _ => [])
  let d:= mockDatabase (parsingSignature helper)
  match dfs problem.graph (fun a l => localValidityCheck m d l a)   with
  | Except.error e => Except.error e
  | Except.ok _ =>
    match modelChecker problem.graph.labels problem.program safe with
    | Except.error e => Except.error e
    | Except.ok _ =>
      if mockDatabaseContainedInModel d (List.toSet problem.graph.labels) = true
      then Except.ok ()
      else Except.error "Model does not contain database"

lemma mainCheckGraphMockDatabaseUnitIffSolution {helper: parsingArityHelper} (problem: graphVerificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): mainCheckGraphMockDatabase problem safe = Except.ok () ↔ (List.toSet problem.graph.labels) = proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) ∧ isAcyclic problem.graph ∧ (∀ (a:ℕ)(mem: a ∈ problem.graph.vertices), locallyValid problem.program.toFinset (mockDatabase (parsingSignature helper)) a problem.graph mem):=
by
  unfold mainCheckGraphMockDatabase
  simp
  constructor
  intro h
  simp at h
  cases dfs_result: dfs problem.graph (fun a l => localValidityCheck (parseProgramToSymbolSequenceMap problem.program (fun _ => [])) (mockDatabase (parsingSignature helper)) l a) with
  | error e =>
    simp[dfs_result] at h
  | ok _ =>
    simp [dfs_result] at h
    cases modelCheck: modelChecker problem.graph.labels problem.program safe with
    | error e =>
      simp [modelCheck] at h
    | ok _ =>
      simp only [modelCheck] at h
      have db: mockDatabaseContainedInModel (mockDatabase (parsingSignature helper)) (List.toSet problem.graph.labels) = true := by
        by_contra p
        simp [p] at h

      rw [dfs_semantics] at dfs_result
      rcases dfs_result with ⟨acyclic,valid⟩
      rw [modelCheckerUnitIffAllRulesTrue] at modelCheck
      rw [mockDatabaseContainedInModelTrue] at db
      constructor
      apply Set.Subset.antisymm
      apply verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics _ _ _ acyclic
      intro a a_mem
      specialize valid a a_mem
      rw [localValidityCheckUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at valid
      apply valid
      rfl

      rw [SemanticsEquivalence]
      apply leastModel
      unfold model
      constructor
      apply modelCheck
      apply db

      --end semantics
      constructor
      apply acyclic
      intro a a_mem
      specialize valid a a_mem
      rw [localValidityCheckUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at valid
      apply valid
      rfl

  intro h
  rcases h with ⟨semantics, acyclic, valid⟩
  have dfs_result: dfs problem.graph (fun a l =>
      localValidityCheck (parseProgramToSymbolSequenceMap problem.program fun _ => [])
        (mockDatabase (parsingSignature helper)) l a) = Except.ok () := by
    rw [dfs_semantics]
    constructor
    apply acyclic
    intro a a_mem
    rw [localValidityCheckUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)]
    apply valid a a_mem
    rfl
  simp [dfs_result]

  have modelChecker: modelChecker problem.graph.labels problem.program safe = Except.ok () := by
    rw [modelCheckerUnitIffAllRulesTrue]
    intro r rP
    have ismodel: model problem.program.toFinset (mockDatabase (parsingSignature helper)) (List.toSet problem.graph.labels) := by
      rw [semantics]
      apply proofTheoreticSemanticsIsModel
    unfold model at ismodel
    apply And.left ismodel r rP
  simp only [modelChecker]

  unfold mockDatabaseContainedInModel
  simp

def checkValidnessOrderedGraphMockDatabase {helper: parsingArityHelper} (problem: orderedGraphVerificationProblem helper):  Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap problem.program (fun _ => [])
  let d:= mockDatabase (parsingSignature helper)
  validateOrderedProof m d problem.graph

lemma checkValidnessOrderedGraphMockDatabaseIffAllValid {helper: parsingArityHelper} (problem: orderedGraphVerificationProblem helper): checkValidnessOrderedGraphMockDatabase problem = Except.ok () ↔ problem.graph.isValid problem.program.toFinset (mockDatabase (parsingSignature helper)) ∧ (labels problem.graph).toSet ⊆ proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) := by
  unfold checkValidnessOrderedGraphMockDatabase
  simp
  rw [validateOrderedProofIffValidAndSubset]


def mainCheckOrderedGraphMockDatabase {helper: parsingArityHelper} (problem: orderedGraphVerificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap problem.program (fun _ => [])
  let d:= mockDatabase (parsingSignature helper)
  match validateOrderedProof m d problem.graph    with
  | Except.error e => Except.error e
  | Except.ok _ =>
    match modelChecker (labels problem.graph) problem.program safe with
    | Except.error e => Except.error e
    | Except.ok _ =>
      if mockDatabaseContainedInModel d (List.toSet (labels problem.graph)) = true
      then Except.ok ()
      else Except.error "Model does not contain database"

lemma mainCheckOrderedGraphMockDatabaseIffSolutionAndValid {helper: parsingArityHelper} (problem: orderedGraphVerificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): mainCheckOrderedGraphMockDatabase problem safe = Except.ok () ↔ problem.graph.isValid problem.program.toFinset (mockDatabase (parsingSignature helper)) ∧ (labels problem.graph).toSet = proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) := by
  unfold mainCheckOrderedGraphMockDatabase
  simp
  split
  · rename_i s validateResult
    simp
    have validateResult': ¬ validateOrderedProof (parseProgramToSymbolSequenceMap problem.program fun _ => []) (mockDatabase (parsingSignature helper)) problem.graph = Except.ok () := by
      simp[validateResult]
    rw [validateOrderedProofSemantics] at validateResult'
    intro h
    contradiction
  · rename_i validateProof
    rw [validateOrderedProofSemantics] at validateProof
    split
    · rename_i s modelCheckResult
      have modelCheckResult': ¬ modelChecker (labels problem.graph) problem.program safe = Except.ok () := by
        simp [modelCheckResult]
      rw [modelCheckerUnitIffAllRulesTrue] at modelCheckResult'
      simp
      intro _
      by_contra h
      simp at modelCheckResult'
      have model: model (List.toFinset problem.program) (mockDatabase (parsingSignature helper)) (List.toSet (labels problem.graph)) := by
        rw [h]
        apply proofTheoreticSemanticsIsModel
      unfold model at model
      rcases model with ⟨rules, _⟩
      rcases modelCheckResult' with ⟨rule, rule_mem, rule_false⟩
      specialize rules rule rule_mem
      contradiction
    · rename_i modelCheckResult
      have h: mockDatabaseContainedInModel (mockDatabase (parsingSignature helper)) (List.toSet (labels problem.graph)) = true := by
        unfold mockDatabaseContainedInModel
        rfl
      simp [h]
      simp [validateProof]
      apply Set.Subset.antisymm
      · rw [← validateOrderedProofSemantics, validateOrderedProofIffValidAndSubset] at validateProof
        simp [validateProof]
      · rw [SemanticsEquivalence]
        apply leastModel
        unfold model
        constructor
        · rw [modelCheckerUnitIffAllRulesTrue] at modelCheckResult
          exact modelCheckResult
        · rw [mockDatabaseContainedInModelTrue] at h
          exact h


inductive inputFormat where
| trees: inputFormat
| graph: inputFormat
| orderedGraph: inputFormat

structure argsParsed where
  (programFileName: String)
  (complete: Bool)
  (help: Bool)
  (format: inputFormat)

def parseArgsHelper (args: List String) (curr: argsParsed) : Except String argsParsed  :=
  match args with
  | [] =>
    if curr.programFileName == ""
    then Except.error "No program file name provided"
    else Except.ok curr
  | hd::tl =>
    if hd ∈ ["-h", "--help"]
    then Except.ok {programFileName := "", complete := false, help := true, format:= inputFormat.trees}
    else  if hd ∈  ["-c", "-g", "-o"]
          then
            if hd == "-c"
            then parseArgsHelper tl {programFileName := "", complete := true, help := false, format:= curr.format}
            else
              if hd == "-g"
              then  parseArgsHelper tl {programFileName := "", complete := curr.complete , help := false, format:= inputFormat.graph}
              else
                if hd == "-o"
                then  parseArgsHelper tl {programFileName := "", complete := curr.complete , help := false, format:= inputFormat.orderedGraph}
                else
                Except.error ("Unknown argument " ++ hd)
          else
          if tl == []
          then Except.ok {programFileName := hd, complete := curr.complete, help := false, format:= curr.format}
          else Except.error "Too many arguments"

def parseArgs (args: List String): Except String argsParsed := parseArgsHelper args {programFileName := "", complete := false, help:= false, format:= inputFormat.trees}

def printHelp: IO Unit := do
  IO.println "Datalog results validity checker"
  IO.println "Input [Options] <problemFile>"
  IO.println "Arguments"
  IO.println "  <problemFile>: contains a json description of the program and the proof trees"
  IO.println "Options"
  IO.println "  -h --help Help (displayed right now)"
  IO.println "  -g        Use a graph instead of a list of trees as an input via a list of edges (start -- end)"
  IO.println "  -o        Use an topologically ordered graph instead of a list of trees as an input via a list atom and list of natural numbers of predecessors"

  IO.println "  -c        Completeness check: in addition to validating the trees check if result is also a model"

def getTreeProblemFromJson (fileName: String): IO (Except String (verificationProblemSignatureWrapper)) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=problemInput) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (convertProblemInputToVerificationProblem parsedProblem)
  else pure (Except.error "File does not exist")

def main_trees (argsParsed: argsParsed): IO Unit := do
  match ← getTreeProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok transformedInput =>
    let problem := transformedInput.problem
    if argsParsed.complete = true
    then
      IO.println "Completeness check"
      match safe: safetyCheckProgram problem.program with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: rule (parsingSignature transformedInput.helper)), r ∈ problem.program → r.isSafe := by
          rw [safetyCheckProgramUnitIffProgramSafe] at safe
          apply safe
        match mainCheckMockDatabase problem safe' with
        | Except.ok _ => IO.println "Valid result"
        | Except.error msg => IO.println ("Invalid result due to " ++ msg )
    else
      match checkValidnessMockDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to " ++ msg )
      | Except.ok _ => IO.println "Valid result"

def getGraphProblemFromJson (fileName: String): IO (Except String (graphVerificationProblemSignatureWrapper)) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=graphInputProblem) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (convertGraphProblemInputToGraphVerificationProblem parsedProblem)
  else pure (Except.error "File does not exist")


def main_graph (argsParsed: argsParsed): IO Unit := do
  match ← getGraphProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok transformedInput =>
    let problem := transformedInput.problem
    if argsParsed.complete = true
    then
      IO.println "Completeness check"
      match safe: safetyCheckProgram problem.program with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: rule (parsingSignature transformedInput.helper)), r ∈ problem.program → r.isSafe := by
          rw [safetyCheckProgramUnitIffProgramSafe] at safe
          apply safe
        match mainCheckGraphMockDatabase problem safe' with
        | Except.ok _ => IO.println "Valid result"
        | Except.error msg => IO.println ("Invalid result due to " ++ msg )
    else
      match checkValidnessGraphMockDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to " ++ msg )
      | Except.ok _ => IO.println "Valid result"

def getOrderedGraphProblemFromJson (fileName: String): IO (Except String (orderedGraphVerificationProblemSignatureWrapper)) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=orderedGraphInputProblem) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (convertOrderedGraphProblemInputToOrderedGraphVerificationProblem parsedProblem)
  else pure (Except.error "File does not exist")

def main_ordered_graph (argsParsed: argsParsed): IO Unit := do
  match ← getOrderedGraphProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok transformedInput =>
    let problem := transformedInput.problem
    if argsParsed.complete = true
    then
      IO.println "Completeness check"
      match safe: safetyCheckProgram problem.program with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: rule (parsingSignature transformedInput.helper)), r ∈ problem.program → r.isSafe := by
          rw [safetyCheckProgramUnitIffProgramSafe] at safe
          apply safe
        match mainCheckOrderedGraphMockDatabase problem safe' with
        | Except.ok _ => IO.println "Valid result"
        | Except.error msg => IO.println ("Invalid result due to " ++ msg )
    else
      match checkValidnessOrderedGraphMockDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to " ++ msg )
      | Except.ok _ => IO.println "Valid result"


def main(args: List String): IO Unit := do
  match parseArgs args with
  | Except.error e => IO.println e
  | Except.ok argsParsed =>
    if argsParsed.help = true
    then printHelp
    else
      match argsParsed.format with
      | inputFormat.trees => main_trees argsParsed
      | inputFormat.graph => main_graph argsParsed
      | inputFormat.orderedGraph => main_ordered_graph argsParsed
