import BalancedAssortments.NPSATStackGadget
import BalancedAssortments.NPSATStackSlackEmpty
import BalancedAssortments.NPSATStackSlackBound

noncomputable section
namespace BalancedAssortments.NPSATStackGadget
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields

def emptyAtom : Atom Reg := embeddedAtom
  (Structured.program NPSATStackSlack.emptyPatch (.inr .vars) (.inr .wire))
  (finish NPSATStackSlack.emptyPatch) (code_finish _) (program_noChoice _ _ _)
  Sum.inr rightVars output

def complete : Block Reg := .seq build (.atom emptyAtom)
def program : Program Reg (Control complete) := Structured.program complete catalog output

def result (labels : List (List Bool)) (F : BitFormula) : List Bool :=
  NPSATStackSlack.patchedWire labels.length F.length
    (NPSATStackSlack.resultWire labels.length F.length (NPSATStackVariables.output labels F labels []))

def completedStore (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) : Store Reg :=
  Function.update (finalStore labels F fr) output (result labels F)

def completedBudget (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) (B : ℕ) : ℕ :=
  buildBudget labels F fr B+
  3*((NPSATStackVariables.output labels F labels []).length+NPSATStackSlack.totalBudget (labels.length+F.length))+
  2*NPSATSubsetSum.fixedYes.length+11

lemma complete_exec (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) (hF : ∀c∈F,c.length≤3)
    (hfcat : ∀label∈labels,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value label)
    (hfform : ∀c∈F,∀l∈c,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value l.labelBits) :
    ∃t ≤ completedBudget labels F fr B,
      Exec complete (startStore labels F fr) (completedStore labels F fr) t := by
  obtain ⟨t,ht,hr⟩ := build_exec labels F fr B hw hF hfcat hfform
  let vw := NPSATStackVariables.output labels F labels []
  let sw := NPSATStackSlack.resultWire labels.length F.length vw
  obtain ⟨u,hu,hp⟩ := NPSATStackSlack.emptyPatch_exec labels.length F.length [] [] [] [] [] sw
  have he : Exec (.atom emptyAtom) (finalStore labels F fr) (completedStore labels F fr) u := by
    apply embeddedAtom_exec
      (Structured.program NPSATStackSlack.emptyPatch (.inr .vars) (.inr .wire))
      (finish NPSATStackSlack.emptyPatch) (code_finish _) (program_noChoice _ _ _)
      Sum.inr Sum.inr_injective rightVars output (hp.compiles _ _)
      (finalStore labels F fr) (completedStore labels F fr)
    · intro a;rfl
    · intro a
      rcases a with a|a <;> cases a <;>
        simp [completedStore,finalStore,combined,output,result,NPSATStackSlack.store,sw,vw]
    · intro k hk;rcases k with k|k
      · simp [completedStore,output]
      · exact False.elim (hk k rfl)
  refine ⟨t+u+1,?_,hr.seq he⟩
  have hlen := NPSATStackSlack.resultWire_length labels.length F.length vw
  rw [NPSATStackSlack.runtimePolynomial_eval] at hlen
  unfold completedBudget
  dsimp only [sw,vw] at *
  omega

/-- Full finite gadget construction, including the positive fixed yes-instance
for the zero-variable, zero-clause boundary. -/
theorem complete_run (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) (hF : ∀c∈F,c.length≤3)
    (hfcat : ∀label∈labels,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value label)
    (hfform : ∀c∈F,∀l∈c,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value l.labelBits) :
    ∃t ≤ completedBudget labels F fr B,
      Run program t ⟨entry complete,startStore labels F fr⟩ ⟨finish complete,completedStore labels F fr⟩ := by
  obtain ⟨t,ht,hr⟩ := complete_exec labels F fr B hw hF hfcat hfform
  exact ⟨t,ht,hr.compiles _ _⟩

lemma noChoice : NoChoice program := program_noChoice _ _ _
lemma completed_output (labels : List (List Bool)) (F : BitFormula) (fr : List Bool) :
    completedStore labels F fr output=result labels F := Function.update_self _ _ _

end BalancedAssortments.NPSATStackGadget
