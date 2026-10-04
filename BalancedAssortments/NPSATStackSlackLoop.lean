import BalancedAssortments.NPSATStackSlackItem

noncomputable section
namespace BalancedAssortments.NPSATStackSlack
open NPStack NPStack.Structured NPStackFields ComplexityTimeBinary

def slackWire : ℕ → ℕ → List Bool → List Bool
  | _,0,wire => wire
  | p,r+1,wire => slackWire (p+1) r
      (FPTASCostProgram.serializeBits (slackBits p r [false,true])++
        FPTASCostProgram.serializeBits (slackBits p r [true])++wire)

def slackNumbers : ℕ → ℕ → List (List Bool)
  | _,0 => []
  | p,r+1 => slackBits p r [true]::slackBits p r [false,true]::slackNumbers (p+1) r

lemma slackWire_eq (p r : ℕ) (wire : List Bool) :
    slackWire p r wire=(slackNumbers p r).reverse.flatMap FPTASCostProgram.serializeBits++wire := by
  induction r generalizing p wire with
  | zero => rfl
  | succ r ih => simp [slackWire,slackNumbers,ih,List.reverse_cons,List.flatMap_append,List.append_assoc]

lemma itemBudget_mono {a b : ℕ} (h : a ≤ b) : itemBudget a ≤ itemBudget b := by
  unfold itemBudget emitBudget
  have h1 : a+1+1 ≤ b+1+1 := by omega
  have h2 : (a+1)*12+4 ≤ (b+1)*12+4 := by omega
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left 1100 h1) h2
  omega

lemma slackBody_exec (vars clauses wire : List Bool) (p r : ℕ) :
    ∃t ≤ 2*itemBudget (p+r)+4,Exec slackBody
      (store vars clauses (List.replicate p false) (List.replicate r false) [] [] [] wire)
      (store vars clauses (List.replicate (p+1) false) (List.replicate r false) [] [] []
        (FPTASCostProgram.serializeBits (slackBits p r [false,true])++
          FPTASCostProgram.serializeBits (slackBits p r [true])++wire)) t := by
  obtain ⟨a,ha,har⟩ := item_exec vars clauses wire [true] p r (by decide)
  obtain ⟨b,hb,hbr⟩ := item_exec vars clauses
    (FPTASCostProgram.serializeBits (slackBits p r [true])++wire) [false,true] p r (by decide)
  have hp := Exec.push (store vars clauses (List.replicate p false) (List.replicate r false) [] [] []
    (FPTASCostProgram.serializeBits (slackBits p r [false,true])++(FPTASCostProgram.serializeBits (slackBits p r [true])++wire)))
    (.inr Extra.pre) false
  refine ⟨a+b+3,by omega,?_⟩
  simpa [slackBody,store,update_prefix,List.replicate_succ,List.append_assoc] using har.seq (hbr.seq hp)

def slackBudget (N r : ℕ) : ℕ := r*(2*itemBudget N+10)+1

theorem slackLoop_exec (vars clauses wire : List Bool) (p r N : ℕ) (hN : p+r ≤ N) :
    ∃t ≤ slackBudget N r,Exec slackLoop
      (store vars clauses (List.replicate p false) (List.replicate r false) [] [] [] wire)
      (store vars clauses (List.replicate (p+r) false) [] [] [] [] (slackWire p r wire)) t := by
  induction r generalizing p wire with
  | zero =>
    refine ⟨1,by simp [slackBudget],?_⟩
    simpa [slackLoop,slackWire] using (Exec.loop_nil (k:=Sum.inr Extra.remaining) (f:=slackBody) (t:=slackBody)
      (s:=store vars clauses (List.replicate p false) [] [] [] [] wire) rfl)
  | succ r ih =>
    obtain ⟨a,ha,har⟩ := slackBody_exec vars clauses wire p r
    obtain ⟨b,hb,hbr⟩ := ih
      (FPTASCostProgram.serializeBits (slackBits p r [false,true])++FPTASCostProgram.serializeBits (slackBits p r [true])++wire)
      (p+1) (by omega)
    have he : Exec slackLoop
        (store vars clauses (List.replicate p false) (List.replicate (r+1) false) [] [] [] wire)
        (store vars clauses (List.replicate (p+1+r) false) [] [] [] [] (slackWire p (r+1) wire)) (a+b+2) := by
      apply Exec.loop_false (bs:=List.replicate r false)
      · simp [store,List.replicate_succ]
      · simpa only [update_remaining] using har
      · exact hbr
    refine ⟨a+b+2,?_,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he⟩
    have hm:=itemBudget_mono (show p+r ≤ N by omega)
    unfold slackBudget at *
    nlinarith

def resultWire (n m : ℕ) (wire : List Bool) : List Bool :=
  FPTASCostProgram.serializeBits (targetBits n m)++slackWire n m wire

def buildBudget (n m : ℕ) : ℕ := slackBudget (n+m) m+emitBudget (n+m)+40*(n+m)+30

theorem build_exec (n m : ℕ) (wire : List Bool) :
    ∃t ≤ buildBudget n m,Exec build
      (store (List.replicate n false) (List.replicate m false) [] [] [] [] [] wire)
      (store (List.replicate n false) (List.replicate m false) [] [] [] [] [] (resultWire n m wire)) t := by
  let vars:=List.replicate n false
  let clauses:=List.replicate m false
  have hc:=copyAtom_run (K:=Reg) (.inr .vars) (.inr .scratch) (.inr .pre)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store vars clauses [] [] [] [] [] wire) rfl
  have hc1 : Exec (.atom (copyAtom (.inr .vars) (.inr .scratch) (.inr .pre)))
      (store vars clauses [] [] [] [] [] wire) (store vars clauses vars [] [] [] [] wire) (5*n+2) := by
    simpa only [store,vars,update_prefix,List.append_nil,List.length_replicate] using hc
  have hc:=copyAtom_run (K:=Reg) (.inr .clauses) (.inr .scratch) (.inr .remaining)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap])
    (store vars clauses vars [] [] [] [] wire) rfl
  have hc2 : Exec (.atom (copyAtom (.inr .clauses) (.inr .scratch) (.inr .remaining)))
      (store vars clauses vars [] [] [] [] wire) (store vars clauses vars clauses [] [] [] wire) (5*m+2) := by
    simpa only [store,clauses,update_remaining,List.append_nil,List.length_replicate] using hc
  obtain ⟨a,ha,har⟩ := slackLoop_exec vars clauses wire n m (n+m) (by omega)
  have hclear:=clearStack_exec (.inr Extra.pre : Reg)
    (store vars clauses (List.replicate (n+m) false) [] [] [] [] (slackWire n m wire))
  have hc3 : Exec (clearStack (.inr .pre))
      (store vars clauses (List.replicate (n+m) false) [] [] [] [] (slackWire n m wire))
      (store vars clauses [] [] [] [] [] (slackWire n m wire)) (3*(n+m)+1) := by
    simpa only [store,update_prefix,List.length_replicate] using hclear
  obtain ⟨b,hb,hbr⟩ := target_exec n m (slackWire n m wire)
  refine ⟨_,?_,hc1.seq (hc2.seq (har.seq (hc3.seq hbr)))⟩
  unfold buildBudget
  omega

theorem build_run (n m : ℕ) (wire : List Bool) :
    ∃t ≤ buildBudget n m,Run program t
      ⟨entry build,store (List.replicate n false) (List.replicate m false) [] [] [] [] [] wire⟩
      ⟨finish build,store (List.replicate n false) (List.replicate m false) [] [] [] [] [] (resultWire n m wire)⟩ := by
  obtain ⟨t,ht,hr⟩ := build_exec n m wire
  exact ⟨t,ht,hr.compiles _ _⟩

lemma noChoice : NoChoice program := program_noChoice _ _ _

theorem accepting_result (n m : ℕ) (wire : List Bool) {t : ℕ} {out : Config Reg (Control build)}
    (hr : Run program t ⟨entry build,store (List.replicate n false) (List.replicate m false) [] [] [] [] [] wire⟩ out)
    (ha : accepts program out) :
    out=⟨finish build,store (List.replicate n false) (List.replicate m false) [] [] [] [] [] (resultWire n m wire)⟩ ∧
      t ≤ buildBudget n m := by
  obtain ⟨u,hu,hur⟩ := build_run n m wire
  have hh := hr.halted_unique (noChoice_deterministic noChoice) hur ha (code_finish build)
  exact ⟨hh.2,hh.1 ▸ hu⟩

end BalancedAssortments.NPSATStackSlack
