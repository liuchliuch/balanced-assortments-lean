import BalancedAssortments.DirectVerifierAlgebra

namespace BalancedAssortments.DirectVerifier
open ComplexityTimeVerifier

abbrev SumBits := ZBits×ZBits

def decodeSum (a : SumBits) : ℤ×ℤ := (zvalue a.1,zvalue a.2)
def sumWidth (a : SumBits) : ℕ := max (width a.1) (width a.2)

def sumStepBits (acc term : SumBits) : SumBits×ℕ :=
  let d := zmul term.1 acc.1
  let a := zmul term.1 acc.2
  let b := zmul term.2 acc.1
  let n := zadd a.1 b.1
  ((d.1,n.1),d.2+a.2+b.2+n.2+8)

@[simp] theorem sumStepBits_decode (acc term : SumBits) :
    decodeSum (sumStepBits acc term).1=sumStep (decodeSum acc) (decodeSum term) := by
  simp [decodeSum,sumStepBits,sumStep,zadd_value,zmul_value]

theorem sumStepBits_width (acc term : SumBits) {A B : ℕ}
    (ha : sumWidth acc≤A) (ht : sumWidth term≤B) :
    sumWidth (sumStepBits acc term).1≤A+2*B+2 := by
  have hd := zmul_width term.1 acc.1
  have ha' := zmul_width term.1 acc.2
  have hb := zmul_width term.2 acc.1
  have hn := zadd_width (zmul term.1 acc.2).1 (zmul term.2 acc.1).1
  dsimp only [sumWidth] at ha ht
  dsimp only [sumStepBits,sumWidth]
  omega

def sumStepCost (A B : ℕ) := 1200*(A+B+1)^2+32*(A+2*B+1)+13

theorem sumStepBits_cost (acc term : SumBits) {A B : ℕ}
    (ha : sumWidth acc≤A) (ht : sumWidth term≤B) :
    (sumStepBits acc term).2≤sumStepCost A B := by
  have hd := zmul_cost term.1 acc.1
  have hca := zmul_cost term.1 acc.2
  have hcb := zmul_cost term.2 acc.1
  have hn := zadd_cost (zmul term.1 acc.2).1 (zmul term.2 acc.1).1
  have hwa := zmul_width term.1 acc.2
  have hwb := zmul_width term.2 acc.1
  dsimp only [sumWidth] at ha ht
  have hd' : (zmul term.1 acc.1).2≤400*(A+B+1)^2 := hd.trans (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left (by omega) 2))
  have hca' : (zmul term.1 acc.2).2≤400*(A+B+1)^2 := hca.trans (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left (by omega) 2))
  have hcb' : (zmul term.2 acc.1).2≤400*(A+B+1)^2 := hcb.trans (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left (by omega) 2))
  have hn' : (zadd (zmul term.1 acc.2).1 (zmul term.2 acc.1).1).2≤32*(A+2*B+1)+5 := by omega
  dsimp only [sumStepBits,sumStepCost]
  omega

def sumFoldBits : List SumBits→SumBits→SumBits×ℕ
  | [],acc => (acc,1)
  | t::ts,acc => let s := sumStepBits acc t; let r := sumFoldBits ts s.1; (r.1,s.2+r.2+4)

theorem sumFoldBits_decode (ts : List SumBits) (acc : SumBits) :
    decodeSum (sumFoldBits ts acc).1=sumFold (ts.map decodeSum) (decodeSum acc) := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t ts ih => simp [sumFoldBits,sumFold,ih]

theorem sumFoldBits_width (ts : List SumBits) (acc : SumBits) {A B : ℕ}
    (ha : sumWidth acc≤A) (ht : ∀ t ∈ ts,sumWidth t≤B) :
    sumWidth (sumFoldBits ts acc).1≤A+ts.length*(2*B+2) := by
  induction ts generalizing acc A with
  | nil => simpa [sumFoldBits] using ha
  | cons t ts ih =>
    have hh := ih (sumStepBits acc t).1 (sumStepBits_width acc t ha (ht t (by simp)))
      (fun u hu => ht u (by simp [hu]))
    simp only [sumFoldBits,List.length_cons]
    nlinarith

theorem sumFoldBits_cost (ts : List SumBits) (acc : SumBits) {A B : ℕ}
    (ha : sumWidth acc≤A) (ht : ∀ t ∈ ts,sumWidth t≤B) :
    (sumFoldBits ts acc).2≤ts.length*(sumStepCost (A+ts.length*(2*B+2)) B+4)+1 := by
  induction ts generalizing acc A with
  | nil => simp [sumFoldBits]
  | cons t ts ih =>
    have hw := sumStepBits_width acc t ha (ht t (by simp))
    have hc := sumStepBits_cost acc t ha (ht t (by simp))
    have hh := ih (sumStepBits acc t).1 hw (fun u hu => ht u (by simp [hu]))
    have hm : sumStepCost A B≤sumStepCost (A+(ts.length+1)*(2*B+2)) B := by
      unfold sumStepCost
      gcongr <;> omega
    have he : A+2*B+2+ts.length*(2*B+2)=A+(ts.length+1)*(2*B+2) := by ring
    rw [he] at hh
    simp only [sumFoldBits,List.length_cons]
    nlinarith

end BalancedAssortments.DirectVerifier
