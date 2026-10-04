import BalancedAssortments.NPCNFStackChainCorrect
import BalancedAssortments.NPStackFieldsRun

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields Encoding ComplexityTimeBinary

lemma gate_data_length (a b : BitLiteral) (z : List Bool) :
    (bodyData (bitGate a b z)).length=4*a.labelBits.length+4*b.labelBits.length+6*z.length+40 := by
  simp [bodyData,bodyFields,bitGate,clauseFields,dataFields,tagBits_length,BitLiteral.neg,bitPositive,bitNegative]
  omega

lemma unit_data_length (a : BitLiteral) : (bodyData [[a]]).length=2*a.labelBits.length+8 := by
  simp [bodyData,bodyFields,clauseFields,dataFields,tagBits_length]
  omega

lemma nextBits_length (z : List Bool) : (nextBits z).length≤z.length+2 := by
  simp only [nextBits,addCarry_length,List.length_cons,List.length_nil]
  omega

lemma emitCost_bound (s : Register → List Bool) (jobs : List (Job StackGate.Register)) (W : ℕ)
    (h : ∀ k,(regs s k).length≤W) : emitCost s jobs≤jobs.length*(10*W+9) := by
  induction jobs with
  | nil => simp [emitCost]
  | cons j js ih =>
    have hj : emitJobCost s j≤10*W+9 := by
      cases j with
      | bit b => simp [emitJobCost]
      | field k => dsimp only [emitJobCost];have := h k;omega
    simp only [emitCost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

lemma appendCost_bound (block : Block) (a b z out : List Bool) (W : ℕ)
    (ha : a.length≤W) (hb : b.length≤W) (hz : z.length≤W) :
    appendCost block a b z out≤4*out.length+40*(10*W+9)+3 := by
  have he := emitCost_bound (store [] a b z [] []) (blockJobs block) W
    (by intro k;cases k <;> assumption)
  have hl := blockJobs_length block
  unfold appendCost
  nlinarith

lemma resetCost_bound (a b z : List Bool) (W : ℕ)
    (ha : a.length≤W) (hb : b.length≤W) (hz : z.length≤W) : resetCost a b z≤100*(W+1) := by
  have hn := nextBits_length z
  have hm : max z.length 1≤W+1 := by omega
  unfold resetCost
  omega

/-- Uniform polynomial cost of the actual finite OR-chain program. W controls
stored label widths plus the at-most-two-bit-per-increment growth, never label
magnitudes. Existing output is fully charged at every append. -/
theorem chainCost_bound (next : List Bool) (a : BitLiteral) (rest : BitClause) (out : List Bool)
    (W : ℕ) (ha : a.labelBits.length≤W) (hr : ∀ b∈rest,b.labelBits.length≤W)
    (hz : next.length+2*rest.length≤W) :
    chainCost next a rest out ≤ (rest.length+1)*(4*out.length+2000*(rest.length+1)*(W+1)) := by
  induction rest generalizing next a out with
  | nil =>
    have hc := appendCost_bound (.unit a.positive) a.labelBits [] next out W ha (by simp) (by simpa using hz)
    simp only [chainCost,List.length_nil]
    nlinarith
  | cons b bs ih =>
    have hb := hr b (by simp)
    have hnext := nextBits_length next
    have hnextW : (nextBits next).length+2*bs.length≤W := by
      simp only [List.length_cons] at hz
      omega
    have hzW : next.length≤W := by omega
    have ht := ih (nextBits next) (bitPositive next) (out++bodyData (bitGate a b next))
      hzW (fun c hc=>hr c (by simp [hc])) hnextW
    have hg := gate_data_length a b next
    have hc := appendCost_bound (.gate a.positive b.positive) a.labelBits b.labelBits next out W ha hb hzW
    have hreset := resetCost_bound a.labelBits b.labelBits next W ha hb hzW
    simp only [List.length_append,hg] at ht
    simp only [chainCost,List.length_cons]
    nlinarith

end BalancedAssortments.NPCNF.StackChain
