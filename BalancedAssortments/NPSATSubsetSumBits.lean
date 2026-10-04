import BalancedAssortments.NPSATSubsetSumCatalog
import BalancedAssortments.NPCNFValidation
import BalancedAssortments.ComplexityTimeReduction

namespace BalancedAssortments.NPSATSubsetSum
open ComplexityTimeBinary NPCNF.Encoding

/-- Horner evaluation of little-endian base-ten digits, using actual bit-list
multiplication and addition. No decoded integer arithmetic is executed. -/
def packBits : List (List Bool) → List Bool × ℕ
  | [] => ([],1)
  | d::ds =>
    let tail := packBits ds
    let shifted := mulBits [false,true,false,true] tail.1
    let added := addCarry d shifted.1 false
    (added.1,tail.2+shifted.2+added.2+8)

lemma packBits_value (ds : List (List Bool)) :
    value (packBits ds).1 = Nat.ofDigits 10 (ds.map value) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [packBits,addCarry_value,mulBits_value,value,ih,Nat.ofDigits_cons]

lemma packBits_length (ds : List (List Bool)) (B : ℕ) (h : ∀ d ∈ ds,d.length≤B) :
    (packBits ds).1.length ≤ ds.length*(B+9) := by
  induction ds with
  | nil => simp [packBits]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    have hm := mulBits_length [false,true,false,true] (packBits ds).1
    have ha := addCarry_length d (mulBits [false,true,false,true] (packBits ds).1).1 false
    simp only [List.length_cons,List.length_nil] at hm
    have hmax : max d.length (mulBits [false,true,false,true] (packBits ds).1).1.length ≤ B+8+ds.length*(B+9) := by omega
    simp only [packBits,List.length_cons]
    nlinarith only [ha,hmax]

lemma packBits_cost (ds : List (List Bool)) (B : ℕ) (h : ∀ d ∈ ds,d.length≤B) :
    (packBits ds).2 ≤ 4096*(ds.length+1)^2*(B+10)^2 := by
  induction ds with
  | nil => simp only [packBits,List.length_nil]; nlinarith [Nat.zero_le B]
  | cons d ds ih =>
    have hd := h d (by simp)
    have hh : ∀ d ∈ ds,d.length≤B := fun d hd => h d (by simp [hd])
    have ht := ih hh
    have hl := packBits_length ds B hh
    have hm := mulBits_cost [false,true,false,true] (packBits ds).1
    have hw := mulBits_length [false,true,false,true] (packBits ds).1
    have ha := addCarry_cost d (mulBits [false,true,false,true] (packBits ds).1).1 false
    norm_num only [List.length_cons,List.length_nil,Nat.zero_add,Nat.reduceAdd] at hm hw
    have hmax : max d.length (mulBits [false,true,false,true] (packBits ds).1).1.length ≤ B+8+ds.length*(B+9) := by omega
    simp only [packBits,List.length_cons]
    try dsimp only
    nlinarith only [ht,hl,hm,ha,hmax]

/-- Count one literal's occurrences using binary semantic label comparison;
repeated literals are counted separately. -/
def occurrenceBits (label : List Bool) (polarity : Bool) : BitClause → List Bool × ℕ
  | [] => ([],1)
  | l::ls =>
    let eq := compareBits l.labelBits label
    let tail := occurrenceBits label polarity ls
    if eq.1 = .eq ∧ l.positive=polarity then
      let up := addCarry tail.1 [true] false
      (up.1,eq.2+tail.2+up.2+6)
    else (tail.1,eq.2+tail.2+4)

def occurrenceCount (label : ℕ) (polarity : Bool) (c : BitClause) : ℕ :=
  c.countP (fun l => decide (value l.labelBits=label ∧ l.positive=polarity))

lemma occurrenceBits_value (label : List Bool) (polarity : Bool) (c : BitClause) :
    value (occurrenceBits label polarity c).1 = occurrenceCount (value label) polarity c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    simp only [occurrenceBits]
    split_ifs with h
    · have hh : value l.labelBits=value label ∧ l.positive=polarity := ⟨(compare_eq_iff _ _).mp h.1,h.2⟩
      simp [addCarry_value,value,ih,occurrenceCount,List.countP_cons,hh]
    · have hh : ¬(value l.labelBits=value label ∧ l.positive=polarity) := by
        intro hh; exact h ⟨(compare_eq_iff _ _).mpr hh.1,hh.2⟩
      simp [ih,occurrenceCount,List.countP_cons,hh]

lemma occurrenceBits_length (label : List Bool) (polarity : Bool) (c : BitClause) :
    (occurrenceBits label polarity c).1.length≤c.length+1 := by
  induction c with
  | nil => simp [occurrenceBits]
  | cons l ls ih =>
    simp only [occurrenceBits,List.length_cons]
    split_ifs
    · have h := addCarry_length (occurrenceBits label polarity ls).1 [true] false
      simp only [List.length_cons,List.length_nil] at h
      dsimp only
      omega
    · dsimp only; omega

lemma occurrenceBits_cost (label : List Bool) (polarity : Bool) (c : BitClause) (B : ℕ)
    (hl : label.length≤B) (hc : ∀ l ∈ c,l.labelBits.length≤B) :
    (occurrenceBits label polarity c).2 ≤ 64*(c.length+1)^2*(B+1) := by
  induction c with
  | nil => simp only [occurrenceBits,List.length_nil]; nlinarith [Nat.zero_le B]
  | cons l ls ih =>
    have hh := hc l (by simp)
    have ht := ih (fun l hl => hc l (by simp [hl]))
    have hw := occurrenceBits_length label polarity ls
    have he := compareBits_cost l.labelBits label
    have ha := addCarry_cost (occurrenceBits label polarity ls).1 [true] false
    have hm : max l.labelBits.length label.length≤B := max_le hh hl
    have hma : max (occurrenceBits label polarity ls).1.length 1 ≤ ls.length+1 := by omega
    norm_num only [List.length_cons,List.length_nil,Nat.zero_add,Nat.reduceAdd] at ha
    simp only [occurrenceBits,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith only [ht,he,ha,hm,hma]

end BalancedAssortments.NPSATSubsetSum
