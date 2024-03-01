import Std.Data.List.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.Basic
import CertifyingDatalog.GraphValidation
import Lean.Data.Json.FromToJson

def NatToString (n: ℕ): String :=
  match n with
  | 0 => " "
  | Nat.succ n => "I" ++ NatToString n

def tokenizeHelper (s: List Char) (currToken: Option String) (tokens: List String): List String :=
  match s with
  | List.nil =>
    match currToken with
    | Option.none => tokens
    | Option.some token => tokens.concat token
  | List.cons hd tl =>
    if (hd ∈ ['(', ')'])
      then
        match currToken with
        | Option.none => tokenizeHelper tl Option.none (tokens.append [hd.toString])
        | Option.some token => tokenizeHelper tl Option.none (tokens.append [token, hd.toString])
      else  if hd ∈ [' ', ',']
            then
               match currToken with
                | Option.none => tokenizeHelper tl Option.none tokens
                | Option.some token => tokenizeHelper tl Option.none (tokens.append [token])
            else
              match currToken with
              | Option.none => tokenizeHelper tl hd.toString tokens
              | Option.some token => tokenizeHelper tl (token.push hd) tokens

def tokenize (s: String): List String := tokenizeHelper s.data Option.none List.nil

inductive mockTerm
| constant: String → mockTerm
| variable: String → mockTerm
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

def mockTerm.toString (mt: mockTerm): String :=
  match mt with
  | mockTerm.constant c => "constant " ++ c
  | mockTerm.variable v => "variable " ++ v

def mockTermList.toString (l: List mockTerm): String :=
  match l with
  | [] => ""
  | hd::tl => mockTerm.toString hd ++ "," ++ mockTermList.toString tl

--#eval Lean.toJson (mockTerm.constant "b")

structure mockAtom where
  (symbol: String)
  (terms: List mockTerm)
deriving DecidableEq, Lean.FromJson, Lean.ToJson, Repr

def mockAtom.toString (ma: mockAtom): String := ma.symbol ++ "(" ++ mockTermList.toString ma.terms ++ ")"

--#eval Lean.toJson (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"])

structure mockRule where
  head: mockAtom
  body: List (mockAtom)
deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

inductive jsonTree (A: Type)
| node (label: A) (children: List (jsonTree A))
deriving Lean.FromJson, Lean.ToJson

structure problemInput where
  (trees: List (jsonTree mockAtom))
  (program: List (mockRule))
deriving Lean.FromJson, Lean.ToJson

structure parsingArityHelper where
  (relationList: List String)
  (arity: {x // x ∈ relationList} → Nat)

def emptyParsingArityHelper: parsingArityHelper := {relationList:= [], arity:= fun _ => 0}

def extendParsingArityHelper (sig: parsingArityHelper) (symbol: String) (arity: Nat): Except String parsingArityHelper :=
  if h: symbol ∈ sig.relationList
  then
    if sig.arity (Subtype.mk symbol h) == arity
    then
      Except.ok sig
    else
      Except.error ("Mismatched arity for " ++ symbol ++ " Given ")
  else
    Except.ok {relationList := sig.relationList ++ [symbol], arity := (fun x => if q:(x = symbol) then arity else
      have p: x.val ∈ sig.relationList := by
        have h': x.val ∈ (sig.relationList ++ [symbol] )
        apply x.property
        simp at h'
        cases h' with
        | inl h' =>
          apply h'
        | inr h' =>
          exact absurd h' q

     sig.arity (Subtype.mk x.val p))}

def parsingSignature (helper: parsingArityHelper): signature :=
  {constants:= String, vars:= String, relationSymbols := {x // x ∈ helper.relationList}, relationArity := helper.arity}

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).constants :=
by
  unfold parsingSignature
  simp
  apply instDecidableEqString

instance (helper: parsingArityHelper): Inhabited (parsingSignature helper).constants :=
by
  unfold parsingSignature
  simp
  use ['a']

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).vars :=
by
  unfold parsingSignature
  simp
  apply instDecidableEqString

instance (helper: parsingArityHelper): DecidableEq (parsingSignature helper).relationSymbols :=  Subtype.instDecidableEqSubtype

instance (helper: parsingArityHelper): Hashable (parsingSignature helper).relationSymbols :=  instHashableSubtype

instance (helper: parsingArityHelper): Hashable (parsingSignature helper).constants :=  instHashableString

instance (helper: parsingArityHelper): Hashable (parsingSignature helper).vars :=  instHashableString

instance (helper: parsingArityHelper): ToString (parsingSignature helper).relationSymbols :=  instToStringSubtype

instance (helper: parsingArityHelper): ToString (parsingSignature helper).constants :=  instToStringString

instance (helper: parsingArityHelper): ToString (parsingSignature helper).vars :=  instToStringString

def getArityHelperFromMockAtom (helper: parsingArityHelper) (ma: mockAtom): Except String parsingArityHelper := extendParsingArityHelper helper ma.symbol (ma.terms.length)

def getArityHelperFromMockAtomList (helper: parsingArityHelper) (l: List mockAtom): Except String parsingArityHelper :=
  match l with
  | [] => Except.ok helper
  | hd::tl =>
    match getArityHelperFromMockAtom helper hd with
    | Except.error e => Except.error e
    | Except.ok newHelper =>
      getArityHelperFromMockAtomList newHelper tl

def getArityHelperFromMockRule (helper: parsingArityHelper) (mr: mockRule): Except String parsingArityHelper :=
  match getArityHelperFromMockAtom helper mr.head with
  | Except.error e => Except.error e
  | Except.ok newHelper => getArityHelperFromMockAtomList newHelper mr.body

def getArityHelperFromProgram.go (helper: parsingArityHelper) (l: List mockRule): Except String parsingArityHelper :=
  match l with
  | [] => Except.ok helper
  | hd::tl =>
    match getArityHelperFromMockRule helper hd with
    | Except.error e => Except.error e
    | Except.ok newHelper => getArityHelperFromProgram.go newHelper tl

def getArityHelperFromProgram (l: List mockRule): Except String parsingArityHelper := getArityHelperFromProgram.go emptyParsingArityHelper l

def transformMockTermToTerm (helper: parsingArityHelper) (mt: mockTerm): term (parsingSignature helper) :=
  match mt with
  | mockTerm.constant c => term.constant c
  | mockTerm.variable v => term.variableDL v

def transformMockTermToConstant (helper: parsingArityHelper) (mt: mockTerm): Except String (parsingSignature helper).constants :=
  match mt with
  | mockTerm.constant c => Except.ok c
  | mockTerm.variable v => Except.error ("Encountered variable" ++ v ++ "in ground atom ")

def transformMockAtomToAtom (helper: parsingArityHelper) (ma: mockAtom): Except String (atom (parsingSignature helper)) :=
  if h: ma.symbol ∈ helper.relationList
  then
    if p: helper.arity (Subtype.mk ma.symbol h) = ma.terms.length
    then
      have q: List.length (List.map (transformMockTermToTerm helper) ma.terms) =
    signature.relationArity (parsingSignature helper) { val := ma.symbol, property := h } := by
        rw [List.length_map]
        rw [← p]
        unfold parsingSignature
        simp

    Except.ok {symbol := (Subtype.mk ma.symbol h), atom_terms := List.map (transformMockTermToTerm helper) ma.terms, term_length := q}
    else Except.error ("Wrong arity for " ++ ma.toString ++ "Expected " ++ NatToString (helper.arity (Subtype.mk ma.symbol h)) ++ "Actually " ++  NatToString ma.terms.length)
  else Except.error ("Unknown symbol" ++ ma.symbol)

def transformMockAtomToGroundAtom (helper: parsingArityHelper) (ma: mockAtom): Except String (groundAtom (parsingSignature helper)) :=
  if h: ma.symbol ∈ helper.relationList
  then
    if p: helper.arity (Subtype.mk ma.symbol h) = ma.terms.length
    then
      match q: List.map_except (transformMockTermToConstant helper) ma.terms with
      | Except.error msg => Except.error ("Error parsing ground atom" ++ msg)
      | Except.ok l =>

      have length: List.length l = signature.relationArity (parsingSignature helper) { val := ma.symbol, property := h } :=
      by
        unfold parsingSignature
        simp
        rw [p]
        apply Eq.symm
        apply List.map_except_ok_length'
        apply q


    Except.ok {symbol := (Subtype.mk ma.symbol h), atom_terms := l, term_length := length}
    else Except.error ("Transform to groundAtom -- Wrong arity for " ++ ma.toString ++ " Expected " ++ NatToString (helper.arity (Subtype.mk ma.symbol h)) ++ "Actually " ++  NatToString ma.terms.length)
  else Except.error ("Unknown symbol" ++ ma.symbol)

def transformMockRuleToRule (helper: parsingArityHelper) (mr: mockRule): Except String (rule (parsingSignature helper)) :=
  match transformMockAtomToAtom helper mr.head with
  | Except.error e => Except.error e
  | Except.ok head =>
    match List.map_except (transformMockAtomToAtom helper) mr.body with
    | Except.error e => Except.error e
    | Except.ok body => Except.ok {head:= head, body:= body}


def proofTreeFromTree (helper: parsingArityHelper) (t: jsonTree mockAtom) : Except String (proofTree (parsingSignature helper)) :=
  match t with
  | jsonTree.node label children =>
    match transformMockAtomToGroundAtom helper label with
    | Except.ok a =>
      let s:= List.map_except (fun ⟨x, _h⟩  => proofTreeFromTree  helper x) children.attach
      match s with
      | Except.ok l =>
        Except.ok (tree.node a l)
      | Except.error msg => Except.error msg
    | Except.error msg => Except.error msg
termination_by proofTreeFromTree relationList t => sizeOf t
decreasing_by
  simp_wf
  decreasing_trivial
  apply Nat.zero_le

structure verificationProblem (helper: parsingArityHelper) where
  (trees: List (proofTree (parsingSignature helper)))
  (program: List (rule (parsingSignature helper)))

structure verificationProblemSignatureWrapper where
  (helper: parsingArityHelper)
  (problem: verificationProblem helper)

def convertProblemInputToVerificationProblem (input: problemInput): Except String verificationProblemSignatureWrapper :=
  match getArityHelperFromProgram input.program with
  | Except.error e => Except.error ("Error parsing program --" ++ e)
  | Except.ok helper =>
    match List.map_except (proofTreeFromTree helper) input.trees with
  | Except.error e => Except.error ("Error parsing trees -- " ++ e)
  | Except.ok trees =>
    match List.map_except (transformMockRuleToRule helper) input.program with
    | Except.error e => Except.error ("Error parsing program -- " ++ e)
    | Except.ok program => Except.ok {helper := helper, problem := {trees := trees, program := program}}


-- graph validation
structure edge where
  (start_node: mockAtom)
  (end_node: mockAtom)
deriving DecidableEq, Lean.FromJson, Lean.ToJson

--#eval Lean.toJson (edge.mk (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"]) (mockAtom.mk "R" [mockTerm.constant "c", mockTerm.variable "v"]))

structure mockGraph where
  (vertices: List mockAtom)
  (edges: List edge)
deriving Lean.FromJson, Lean.ToJson

structure graphInputProblem where
  (graph: mockGraph)
  (program: List mockRule)
deriving Lean.FromJson, Lean.ToJson





def unconnectedGroundAtomGraph (helper: parsingArityHelper) (l:List (groundAtom (parsingSignature helper))): Graph (groundAtom (parsingSignature helper)) :=
  {
    vertices := l,
    predecessors := fun _ => []
    complete :=by simp
  }

def addEdge_helper (helper: parsingArityHelper) (start_node end_node: groundAtom (parsingSignature helper)) (G: Graph (groundAtom (parsingSignature helper))): Graph (groundAtom (parsingSignature helper)) :=
  if start_mem: start_node ∈ G.vertices
  then
    if end_node ∈ G.vertices
    then
      {
        vertices:= G.vertices,
        predecessors := fun  x => if x = end_node then (G.predecessors x) ++ [start_node] else G.predecessors x,
        complete:= by
          intro a a_mem b b_mem
          simp at b_mem
          by_cases a_end: a = end_node
          simp [a_end] at b_mem
          cases b_mem with
          | inr b_start =>
            rw [b_start]
            apply start_mem
          | inl b_end =>
            rw [← a_end] at b_end
            apply G.complete a a_mem b b_end

          simp [a_end] at b_mem
          apply G.complete a a_mem b b_mem
      }
    else
      {
        vertices:= end_node::G.vertices,
        predecessors := fun  x => if x = end_node then [start_node] else G.predecessors x,
        complete:= by
          intro a a_mem b b_mem
          simp at b_mem
          simp
          right
          by_cases a_end: a = end_node
          simp [a_end] at b_mem
          rw [b_mem]
          apply start_mem

          simp [a_end] at b_mem
          simp [a_end] at a_mem
          apply G.complete a a_mem b b_mem
          }
  else
    if end_mem: end_node ∈ G.vertices
    then
      {
        vertices:= start_node::G.vertices,
        predecessors := fun x => if x = end_node then G.predecessors x ++ [start_node] else if x= start_node then [] else (G.predecessors x),
        complete :=by
          intro a a_mem b b_mem
          simp at b_mem
          by_cases a_end: a = end_node
          simp [a_end] at b_mem
          cases b_mem with
          | inr b_start =>
            rw [b_start]
            simp
          | inl b_pred =>
            simp
            right
            apply G.complete end_node end_mem b b_pred

          simp [a_end]
          simp [a_end] at b_mem
          by_cases a_start: a = start_node
          simp [a_start] at b_mem

          simp [a_start] at b_mem
          simp [a_start] at a_mem
          right
          apply G.complete a a_mem b b_mem
      }
    else
      {
        vertices := start_node::end_node::G.vertices,
        predecessors := fun x => if x = end_node then [start_node] else if x = start_node then [] else G.predecessors x,
        complete :=by
          intro a a_mem b b_mem
          simp at b_mem
          by_cases a_end: a = end_node
          simp [a_end] at b_mem
          simp [b_mem]

          simp [a_end] at b_mem
          by_cases a_start: a = start_node
          simp [a_start] at b_mem

          simp [a_start] at b_mem
          simp
          right
          right
          simp [a_end, a_start] at a_mem
          apply G.complete a a_mem b b_mem
      }

def addEdge (helper: parsingArityHelper) (e: edge) (G: Graph (groundAtom (parsingSignature helper))): Except String (Graph (groundAtom (parsingSignature helper))) :=
  match transformMockAtomToGroundAtom helper e.start_node with
  | Except.error msg =>
      Except.error msg
  | Except.ok start_node =>
    match transformMockAtomToGroundAtom helper e.end_node with
    | Except.error msg =>
        Except.error msg
    | Except.ok end_node => Except.ok (addEdge_helper helper start_node end_node G)

def foldl_except {A B: Type} (f: A → B → Except String B) (l: List A) (init: B) :=
  match l with
  | [] => Except.ok init
  | hd::tl =>
    match f hd init with
    | Except.error msg => Except.error msg
    | Except.ok init' => foldl_except f tl init'

def getGraph (helper: parsingArityHelper) (g: mockGraph): Except String (Graph (groundAtom (parsingSignature helper))) :=
  match List.map_except (transformMockAtomToGroundAtom helper) g.vertices with
  | Except.error e => Except.error ("Error parsing vertices -- " ++ e)
  | Except.ok v' =>
  foldl_except (addEdge helper) g.edges (unconnectedGroundAtomGraph helper v')


structure graphVerificationProblem (helper: parsingArityHelper) where
  (graph: Graph (groundAtom (parsingSignature helper)))
  (program: List (rule (parsingSignature helper)))

structure graphVerificationProblemSignatureWrapper where
  (helper: parsingArityHelper)
  (problem: graphVerificationProblem helper)

def convertGraphProblemInputToGraphVerificationProblem (input: graphInputProblem): Except String graphVerificationProblemSignatureWrapper :=
  match getArityHelperFromProgram input.program with
  | Except.error e => Except.error ("Error parsing program --" ++ e)
  | Except.ok helper =>
    match getGraph helper input.graph with
    | Except.error e => Except.error ("Error parsing graph --" ++ e)
    | Except.ok graph =>
      match List.map_except (transformMockRuleToRule helper) input.program with
    | Except.error e => Except.error ("Error parsing program -- " ++ e)
    | Except.ok program => Except.ok {helper := helper, problem := {graph := graph, program := program}}
