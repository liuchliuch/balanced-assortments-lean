import BalancedAssortments.NPCNFStackChainRead

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields Encoding

def bodyData (F : BitFormula) : List Bool := dataFields (bodyFields F)
@[simp] lemma bodyData_append (F G : BitFormula) : bodyData (F++G)=bodyData F++bodyData G := by
  simp [bodyData,bodyFields,dataFields,List.flatMap_append]

lemma emitted_store (i a b z o c o' : List Bool) : emitted (store i a b z o c) o'=store i a b z o' c := by
  funext k;cases k <;> simp [emitted,store]

lemma emitCost_store (i a b z o c : List Bool) (jobs : List (Job StackGate.Register)) :
    emitCost (store i a b z o c) jobs=emitCost (store [] a b z [] []) jobs := by
  have he : regs (store i a b z o c)=regs (store [] a b z [] []) := by funext k;cases k <;> rfl
  unfold emitCost
  congr 1
  apply List.map_congr_left
  intro job hj
  cases job <;> simp [emitJobCost,he]

def appendCost (block : Block) (a b z out : List Bool) : ℕ :=
  4*out.length+emitCost (store [] a b z [] []) (blockJobs block)+3

lemma append_store (initialSign : Bool) (block : Block) (i a b z o c : List Bool) :
    Run (program initialSign) (appendCost block a b z o)
      (cfg (.saveOutput block) (store i a b z o c))
      (cfg (afterBlock block) (store i a b z (o++blockData (store i a b z o c) block) c)) := by
  have hh := append_block initialSign block (store i a b z o c) (store_work _ _ _ _ _ _) rfl
  rw [emitted_store,emitCost_store] at hh
  exact hh

lemma unit_data (i a z o c : List Bool) (sa : Bool) :
    blockData (store i a [] z o c) (.unit sa)=bodyData [[⟨a,sa⟩]] := rfl
lemma gate_data (i a b z o c : List Bool) (sa sb : Bool) :
    blockData (store i a b z o c) (.gate sa sb)=bodyData (bitGate ⟨a,sa⟩ ⟨b,sb⟩ z) := rfl

def chainLast (next : List Bool) (a : BitLiteral) : BitClause → List Bool
  | [] => a.labelBits
  | _::bs => chainLast (nextBits next) (bitPositive next) bs

def chainAllocated (next : List Bool) : BitClause → List Bool
  | [] => []
  | _::bs => chainAllocated (nextBits next) bs++(tagBits next++[false])

def chainCost (next : List Bool) (a : BitLiteral) : BitClause → List Bool → ℕ
  | [],out => 5+appendCost (.unit a.positive) a.labelBits [] next out
  | b::bs,out => 5*b.labelBits.length+15+
      appendCost (.gate a.positive b.positive) a.labelBits b.labelBits next out+
      resetCost a.labelBits b.labelBits next+
      chainCost (nextBits next) (bitPositive next) bs (out++bodyData (bitGate a b next))

/-- Exact refinement of the recursive raw OR-chain by an actual finite
Boolean-stack program. Fresh labels are incremented in bits; every output
append and repeated label copy is included in the explicit execution count. -/
theorem chain_run (initialSign : Bool) (next : List Bool) (a : BitLiteral) (rest : BitClause)
    (suffix out allocated : List Bool) :
    Run (program initialSign) (chainCost next a rest out)
      (cfg (.readSign a.positive) (store (dataFields (clauseFields rest)++suffix) a.labelBits [] next out allocated))
      (cfg .accept (store suffix (chainLast next a rest) [] (bitChain next a rest).1.2
        (out++bodyData (bitChain next a rest).1.1) (chainAllocated next rest++allocated))) := by
  induction rest generalizing next a out allocated with
  | nil =>
    have h1 := read_end initialSign a.positive suffix a.labelBits next out allocated
    have h2 := append_store initialSign (.unit a.positive) suffix a.labelBits [] next out allocated
    rw [unit_data] at h2
    have hh := h1.trans h2
    simpa [chainCost,chainLast,chainAllocated,bitChain,clauseFields,dataFields,tagBits,afterBlock] using hh
  | cons b bs ih =>
    let tail := dataFields (clauseFields bs)++suffix
    let o' := out++bodyData (bitGate a b next)
    have h1 := read_literal initialSign a.positive b.positive tail a.labelBits b.labelBits next out allocated
    have h2 := append_store initialSign (.gate a.positive b.positive) tail a.labelBits b.labelBits next out allocated
    have he : blockData (store tail a.labelBits b.labelBits next out allocated) (.gate a.positive b.positive)=
        bodyData (bitGate a b next) := by cases a;cases b;rfl
    rw [he] at h2
    have h3 := reset_after_gate initialSign tail a.labelBits b.labelBits next o' allocated
    have h4 := ih (nextBits next) (bitPositive next) o' (tagBits next++false::allocated)
    have hh := h1.trans (h2.trans (h3.trans h4))
    simpa [chainCost,chainLast,chainAllocated,bitChain,nextBits,bitPositive,tail,o',
      clauseFields,dataFields,tagBits,bodyData_append,List.append_assoc,Nat.add_assoc] using hh

end BalancedAssortments.NPCNF.StackChain
