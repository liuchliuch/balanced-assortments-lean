import BalancedAssortments.NPSATStackVariableTokens
import BalancedAssortments.NPSATStackSlackLoop

set_option maxHeartbeats 4000000
noncomputable section
namespace BalancedAssortments.NPSATStackGadget
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields
abbrev Reg := NPSATStackVariableTokens.Reg ⊕ NPSATStackSlack.Reg

def catalog : Reg := .inl NPSATStackVariableTokens.catalog
def formula : Reg := .inl NPSATStackVariableTokens.formula
def fresh : Reg := .inl NPSATStackVariableTokens.fresh
def output : Reg := .inr (.inr .wire)
def scratch : Reg := .inr (.inr .scratch)
def leftVars : Reg := .inl NPSATStackVariableTokens.vars
def leftClauses : Reg := .inl NPSATStackVariableTokens.clauses
def leftWire : Reg := .inl NPSATStackVariableTokens.wire
def rightVars : Reg := .inr (.inr .vars)
def rightClauses : Reg := .inr (.inr .clauses)

def variableTokensAtom : Atom Reg := embeddedAtom
  (Structured.program NPSATStackVariableTokens.build NPSATStackVariableTokens.catalog NPSATStackVariableTokens.wire)
  (finish NPSATStackVariableTokens.build) (code_finish _) (program_noChoice _ _ _)
  Sum.inl catalog leftWire

def slackAtom : Atom Reg := embeddedAtom NPSATStackSlack.program
  (finish NPSATStackSlack.build) (code_finish _) NPSATStackSlack.noChoice Sum.inr rightVars output

def build : Block Reg := .seq (.atom variableTokensAtom)
  (.seq (.atom (copyAtom leftVars scratch rightVars))
    (.seq (.atom (copyAtom leftClauses scratch rightClauses))
      (.seq (.atom (copyAtom leftWire scratch output)) (.atom slackAtom))))

def combined (p : Store NPSATStackVariableTokens.Reg) (s : Store NPSATStackSlack.Reg) : Store Reg
  | .inl k => p k | .inr k => s k

@[simp] lemma combined_update_right (p : Store NPSATStackVariableTokens.Reg) (s : Store NPSATStackSlack.Reg)
    (k : NPSATStackSlack.Reg) (v : List Bool) :
    Function.update (combined p s) (.inr k) v=combined p (Function.update s k v) := by
  funext j;rcases j with j|j <;> simp [combined,Function.update]

def startStore (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) : Store Reg :=
  combined (NPSATStackVariableTokens.store [] (dataFields labels) (dataFields (formulaFields F)) fr [] [] [] [])
    (NPSATStackSlack.store [] [] [] [] [] [] [] [])

def finalStore (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) : Store Reg :=
  combined
    (NPSATStackVariableTokens.store [] (dataFields labels) (dataFields (formulaFields F)) fr fr
      (List.replicate labels.length false) (List.replicate F.length false)
      (NPSATStackVariables.output labels F labels []))
    (NPSATStackSlack.store (List.replicate labels.length false) (List.replicate F.length false) [] [] [] [] []
      (NPSATStackSlack.resultWire labels.length F.length (NPSATStackVariables.output labels F labels [])))

def buildBudget (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) (B : ℕ) : ℕ :=
  5*(dataFields labels).length+NPSATStackVariables.budget labels F labels B+
  5*fr.length+NPSATStackItem.tokensBudget labels F fr B+7+
  5*labels.length+5*F.length+5*(NPSATStackVariables.output labels F labels []).length+
  NPSATStackSlack.buildBudget labels.length F.length+10

lemma build_exec (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) (hF : ∀c∈F,c.length≤3)
    (hfcat : ∀label∈labels,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value label)
    (hfform : ∀c∈F,∀l∈c,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value l.labelBits) :
    ∃t ≤ buildBudget labels F fr B,Exec build (startStore labels F fr) (finalStore labels F fr) t := by
  let nt := List.replicate labels.length false
  let mt := List.replicate F.length false
  let vw := NPSATStackVariables.output labels F labels []
  let p0 := NPSATStackVariableTokens.store [] (dataFields labels) (dataFields (formulaFields F)) fr [] [] [] []
  let p1 := NPSATStackVariableTokens.store [] (dataFields labels) (dataFields (formulaFields F)) fr fr nt mt vw
  let s0 := NPSATStackSlack.store [] [] [] [] [] [] [] []
  let s1 := NPSATStackSlack.store nt [] [] [] [] [] [] []
  let s2 := NPSATStackSlack.store nt mt [] [] [] [] [] []
  let s3 := NPSATStackSlack.store nt mt [] [] [] [] [] vw
  let s4 := NPSATStackSlack.store nt mt [] [] [] [] [] (NPSATStackSlack.resultWire labels.length F.length vw)
  obtain ⟨tv,htv,hv⟩ := NPSATStackVariableTokens.build_exec labels F fr [] B hw hF hfcat hfform
  have h1 : Exec (.atom variableTokensAtom) (combined p0 s0) (combined p1 s0) tv := by
    apply embeddedAtom_exec
      (Structured.program NPSATStackVariableTokens.build NPSATStackVariableTokens.catalog NPSATStackVariableTokens.wire)
      (finish NPSATStackVariableTokens.build) (code_finish _) (program_noChoice _ _ _)
      Sum.inl Sum.inl_injective catalog leftWire (hv.compiles _ _) (combined p0 s0) (combined p1 s0)
    · intro a;rfl
    · intro a;rfl
    · intro k hk;rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
  have hcv := copyAtom_run leftVars scratch rightVars
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap,leftVars,scratch,rightVars])
    (combined p1 s0) rfl
  have h2 : Exec (.atom (copyAtom leftVars scratch rightVars)) (combined p1 s0) (combined p1 s1) (5*labels.length+2) := by
    simpa [combined,leftVars,rightVars,p1,s0,s1,nt,NPSATStackVariableTokens.vars,NPSATStackVariableTokens.itemMap,
      NPSATStackVariableTokens.store,NPSATStackItem.store,NPSATStackSlack.store,Function.update] using hcv
  have hcc := copyAtom_run leftClauses scratch rightClauses
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap,leftClauses,scratch,rightClauses])
    (combined p1 s1) rfl
  have h3 : Exec (.atom (copyAtom leftClauses scratch rightClauses)) (combined p1 s1) (combined p1 s2) (5*F.length+2) := by
    simpa [combined,leftClauses,rightClauses,p1,s1,s2,mt,NPSATStackVariableTokens.clauses,NPSATStackVariableTokens.itemMap,
      NPSATStackVariableTokens.store,NPSATStackItem.store,NPSATStackSlack.store,Function.update] using hcc
  have hcw := copyAtom_run leftWire scratch output
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap,leftWire,scratch,output])
    (combined p1 s2) rfl
  have h4 : Exec (.atom (copyAtom leftWire scratch output)) (combined p1 s2) (combined p1 s3) (5*vw.length+2) := by
    simpa [combined,leftWire,output,p1,s2,s3,NPSATStackVariableTokens.wire,NPSATStackVariableTokens.itemMap,
      NPSATStackVariableTokens.store,NPSATStackItem.store,NPSATStackSlack.store,Function.update] using hcw
  obtain ⟨ts,hts,hs⟩ := NPSATStackSlack.build_run labels.length F.length vw
  have h5 : Exec (.atom slackAtom) (combined p1 s3) (combined p1 s4) ts := by
    apply embeddedAtom_exec NPSATStackSlack.program (finish NPSATStackSlack.build) (code_finish _) NPSATStackSlack.noChoice
      Sum.inr Sum.inr_injective rightVars output hs (combined p1 s3) (combined p1 s4)
    · intro a;rfl
    · intro a;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · exact False.elim (hk k rfl)
  refine ⟨_,?_,h1.seq (h2.seq (h3.seq (h4.seq h5)))⟩
  unfold buildBudget
  dsimp only [vw] at *
  omega

end BalancedAssortments.NPSATStackGadget
