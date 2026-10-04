import BalancedAssortments.NPCNFStackTemplateRun
import BalancedAssortments.NPCNFThreeBits

namespace BalancedAssortments.NPCNF.StackTemplate
open NPStack NPStackFields
variable {K : Type*} [DecidableEq K]

inductive FieldSpec (K : Type*) | constant (bits : List Bool) | reg (k : K)

def fieldValue (regs : K → List Bool) : FieldSpec K → List Bool
  | .constant bs => bs
  | .reg k => regs k

def fieldJobs : FieldSpec K → List (Job K)
  | .constant bs => (tagBits bs++[false]).reverse.map Job.bit
  | .reg k => [.field k]

def fieldsJobs (fs : List (FieldSpec K)) : List (Job K) := fs.reverse.flatMap fieldJobs

lemma applyJobs_append (regs : K → List Bool) (a b : List (Job K)) (out : List Bool) :
    applyJobs regs (a++b) out=applyJobs regs b (applyJobs regs a out) := by
  induction a generalizing out <;> simp_all [applyJobs]

lemma applyJobs_bits (regs : K → List Bool) (bs out : List Bool) :
    applyJobs regs (bs.map Job.bit) out=bs.reverse++out := by
  induction bs generalizing out <;> simp_all [applyJobs,applyJob,List.reverse_cons,List.append_assoc]

lemma fieldJobs_apply (regs : K → List Bool) (f : FieldSpec K) (out : List Bool) :
    applyJobs regs (fieldJobs f) out=tagBits (fieldValue regs f)++false::out := by
  cases f with
  | constant bs =>
    change applyJobs regs ((tagBits bs++[false]).reverse.map Job.bit) out = _
    rw [applyJobs_bits]
    simp [fieldValue,List.append_assoc]
  | reg k => rfl

lemma fieldsJobs_apply (regs : K → List Bool) (fs : List (FieldSpec K)) (out : List Bool) :
    applyJobs regs (fieldsJobs fs) out=dataFields (fs.map (fieldValue regs))++out := by
  induction fs generalizing out with
  | nil => simp [fieldsJobs,applyJobs,dataFields]
  | cons f fs ih =>
    simp only [fieldsJobs,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      applyJobs_append,fieldJobs_apply]
    rw [show applyJobs regs (fs.reverse.flatMap fieldJobs) out= dataFields (fs.map (fieldValue regs))++out from ih out]
    simp [dataFields,List.append_assoc]

end BalancedAssortments.NPCNF.StackTemplate

namespace BalancedAssortments.NPCNF.StackGate
open NPStack NPStackFields StackTemplate Encoding
inductive Register | left | right | fresh deriving DecidableEq,Fintype

def gateSpecs (sa sb : Bool) : List (FieldSpec Register) :=
  [.constant [true],.constant [!sa],.reg .left,.constant [true],.reg .fresh,.constant [],
   .constant [true],.constant [!sb],.reg .right,.constant [true],.reg .fresh,.constant [],
   .constant [true],.constant [sa],.reg .left,.constant [sb],.reg .right,.constant [false],.reg .fresh,.constant []]

def gateRegisters (a b : BitLiteral) (z : List Bool) : Register → List Bool
  | .left => a.labelBits
  | .right => b.labelBits
  | .fresh => z

def bodyFields (F : BitFormula) : List (List Bool) := F.flatMap (fun c => [true]::clauseFields c)

def gateProgram (sa sb : Bool) := StackTemplate.program (fieldsJobs (gateSpecs sa sb)) Register.left

lemma gateSpecs_refines (a b : BitLiteral) (z : List Bool) :
    (gateSpecs a.positive b.positive).map (fieldValue (gateRegisters a b z))=bodyFields (bitGate a b z) := rfl

lemma gate_job_count (sa sb : Bool) : (fieldsJobs (gateSpecs sa sb)).length=40 := by
  simp [fieldsJobs,gateSpecs,fieldJobs,tagBits]

def gateCost (a b : BitLiteral) (z : List Bool) : ℕ :=
  jobsCost (gateRegisters a b z) (fieldsJobs (gateSpecs a.positive b.positive))

/-- Literal finite Boolean-stack OR-gate emitter, preserving all three label
registers, appending the exact source bitGate clause fields, and charging every
copied label bit. Sign choices are finite Boolean control parameters. -/
theorem gate_run (a b : BitLiteral) (z out : List Bool) :
    Run (gateProgram a.positive b.positive) (gateCost a b z)
      (cfg (.dispatch 0) (gateRegisters a b z) [] out)
      (cfg (.dispatch (Fin.last (fieldsJobs (gateSpecs a.positive b.positive)).length))
        (gateRegisters a b z) [] (dataFields (bodyFields (bitGate a b z))++out)) := by
  have h := template_run (fieldsJobs (gateSpecs a.positive b.positive)) Register.left (gateRegisters a b z) out
  rw [fieldsJobs_apply,gateSpecs_refines] at h
  exact h

lemma gate_cost_bound (a b : BitLiteral) (z : List Bool) (B : ℕ)
    (ha : a.labelBits.length≤B) (hb : b.labelBits.length≤B) (hz : z.length≤B) :
    gateCost a b z≤40*(6*B+4) := by
  have h := jobsCost_bound (fieldsJobs (gateSpecs a.positive b.positive)) (gateRegisters a b z) B
    (by intro k; cases k <;> assumption)
  simpa only [gateCost,gate_job_count] using h

end BalancedAssortments.NPCNF.StackGate
