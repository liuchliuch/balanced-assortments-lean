import BalancedAssortments.NPCNFStackFormulaCorrect

namespace BalancedAssortments.NPCNF.StackFormula
open NPStack NPStack.Macros StackChain StackGate NPStackFields Encoding

lemma chain_counter_length (next : List Bool) (a : BitLiteral) (rest : BitClause) :
    (bitChain next a rest).1.2.length≤next.length+2*rest.length := by
  induction rest generalizing next a with
  | nil => simp [bitChain]
  | cons b bs ih =>
    have ht := ih (nextBits next) (bitPositive next)
    have hn := nextBits_length next
    simp only [bitChain,List.length_cons]
    change (bitChain (nextBits next) (bitPositive next) bs).1.2.length≤_
    omega

lemma chain_last_width (next : List Bool) (a : BitLiteral) (rest : BitClause) (W : ℕ)
    (ha : a.labelBits.length≤W) (hz : next.length+2*rest.length≤W) : (chainLast next a rest).length≤W := by
  induction rest generalizing next a with
  | nil => exact ha
  | cons b bs ih =>
    apply ih (nextBits next) (bitPositive next) (by change next.length≤W;omega)
    have hn := nextBits_length next
    simp only [List.length_cons] at hz
    omega

lemma chain_body_length (next : List Bool) (a : BitLiteral) (rest : BitClause) (W : ℕ)
    (ha : a.labelBits.length≤W) (hr : ∀ b∈rest,b.labelBits.length≤W)
    (hz : next.length+2*rest.length≤W) :
    (bodyData (bitChain next a rest).1.1).length≤(rest.length+1)*(14*W+40) := by
  induction rest generalizing next a with
  | nil => simp only [bitChain,unit_data_length,List.length_nil];omega
  | cons b bs ih =>
    have hb := hr b (by simp)
    have hn := nextBits_length next
    have hz' : (nextBits next).length+2*bs.length≤W := by simp only [List.length_cons] at hz;omega
    have htail := ih (nextBits next) (bitPositive next) (by change next.length≤W;omega)
      (fun b hb=>hr b (by simp [hb])) hz'
    have hgate := gate_data_length a b next
    simp only [bitChain,bodyData_append,List.length_append,List.length_cons]
    change _+(bodyData (bitChain (nextBits next) (bitPositive next) bs).1.1).length≤_
    nlinarith

def formulaSize (F : BitFormula) : ℕ := (F.map (fun c=>c.length+1)).sum
@[simp] lemma formulaSize_nil : formulaSize []=0 := rfl
@[simp] lemma formulaSize_cons (c : BitClause) (cs : BitFormula) : formulaSize (c::cs)=c.length+1+formulaSize cs := rfl

theorem formulaCost_bound (next : List Bool) (F : BitFormula) (out : List Bool) (W : ℕ)
    (hlabels : ∀ c∈F,∀ l∈c,l.labelBits.length≤W)
    (hwidth : next.length+2*formulaSize F≤W) :
    formulaCost next F out≤(formulaSize F+1)*(4*out.length+10000*(formulaSize F+1)*(W+1)) := by
  induction F generalizing next out with
  | nil => simp only [formulaCost,formulaSize_nil];nlinarith
  | cons c cs ih =>
    have htail : ∀ c∈cs,∀ l∈c,l.labelBits.length≤W := fun c hc=>hlabels c (by simp [hc])
    cases c with
    | nil =>
      have hi := ih next (out++bodyData [[]]) htail (by simp only [formulaSize_cons,List.length_nil] at hwidth;omega)
      have hl : (bodyData ([[]] : BitFormula)).length=4 := rfl
      simp only [List.length_append,hl] at hi
      simp only [formulaCost,formulaSize_cons,List.length_nil]
      nlinarith
    | cons a as =>
      have ha := hlabels (a::as) (by simp) a (by simp)
      have hrest : ∀ b∈as,b.labelBits.length≤W := fun b hb=>hlabels (a::as) (by simp) b (by simp [hb])
      have hz : next.length+2*as.length≤W := by simp only [formulaSize_cons,List.length_cons] at hwidth;omega
      have hcounter := chain_counter_length next a as
      have hnext : (bitChain next a as).1.2.length+2*formulaSize cs≤W := by
        simp only [formulaSize_cons,List.length_cons] at hwidth;omega
      have hi := ih (bitChain next a as).1.2 (out++bodyData (bitChain next a as).1.1) htail hnext
      have hc := chainCost_bound next a as out W ha hrest hz
      have hlast := chain_last_width next a as W ha hz
      have hbody := chain_body_length next a as W ha hrest hz
      simp only [List.length_append] at hi
      simp only [formulaCost,formulaSize_cons,List.length_cons]
      nlinarith [Nat.zero_le (as.length*as.length*W),Nat.zero_le (as.length*formulaSize cs*W)]

end BalancedAssortments.NPCNF.StackFormula
