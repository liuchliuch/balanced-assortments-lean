import BalancedAssortments.ComplexityTimeSourcePipeline

/-! A genuine polynomial bound in the total stored binary input/certificate size,
not merely in dimension and unbounded numeric magnitudes. -/
namespace BalancedAssortments.ComplexityTimeSourcePipeline
open ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open Decomposition.CostMachine

def fractionSize (x : Fraction) : ℕ := x.num.1.length+x.num.2.length+x.den.length+1
def integerSize (x : ZBits) : ℕ := x.1.length+x.2.length+1

def totalInputSize (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : List ZBits) (q : ZBits) : ℕ :=
  v.length+r.length+mask.length+p.length+
    (v.map fractionSize).sum+(r.map fractionSize).sum+fractionSize α+fractionSize H+
    K.length+(p.map integerSize).sum+integerSize q+1

lemma fractionWidth_le_size (x : Fraction) : ComplexityTimeFractions.width x ≤ fractionSize x := by
  unfold ComplexityTimeFractions.width ComplexityTimeVerifier.width fractionSize
  omega
lemma integerWidth_le_size (x : ZBits) : ComplexityTimeVerifier.width x ≤ integerSize x := by
  unfold ComplexityTimeVerifier.width integerSize
  omega

lemma size_mem_le_sum {α : Type*} (f : α → ℕ) (xs : List α) (x : α) (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons,List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have h := ih hx
      omega

theorem sourceBudget_mono {n B C P n' B' C' P' : ℕ}
    (hn : n ≤ n') (hB : B ≤ B') (hC : C ≤ C') (hP : P ≤ P') :
    sourceBudget n B C P ≤ sourceBudget n' B' C' P' := by
  unfold sourceBudget compiledRowBudget assemblyBudget scalarBudget clearingVolume
    inputProductBudget rowBudget enumerationCost
  dsimp only
  gcongr

/-- The explicit natural-coefficient polynomial obtained by substituting the
whole-input bit count for dimension, field width and certificate width/count. -/
noncomputable def sourceTimePolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  let scalar := 4000*(X+2)^2+32*X+50
  let assembly := (X+1)*scalar+8*(X+1)^2
  let volume := (X+1)*(3*X+5)
  let product := 256*(volume+1)^2
  let compiled := assembly+(X+1)*((X+2)*(4*product))+6*(X+1)+9
  let W := 4*volume+1+X
  let checked := (X+X+1)*(5000*(W+1)^2+256*(3*W+2*(X+X)+1)+500)
  let rows := X*X+3*X+2
  rows*(compiled+4)+1+(rows*(checked+4)+48*W+27)+16*(X+1)*rows+4+4+4*X+1

theorem sourceTimePolynomial_eval (L : ℕ) :
    sourceTimePolynomial.eval L = sourceBudget L L L L+4*L+1 := by
  simp only [sourceTimePolynomial,sourceBudget,compiledRowBudget,assemblyBudget,scalarBudget,
    clearingVolume,inputProductBudget,rowBudget,enumerationCost,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_zero]
  ring

/-- Complete source-row construction, clearing and binary verification are
polynomial in total input plus certificate bit size. Field contents may be
arbitrarily large integers; they are processed solely through bit algorithms. -/
theorem verifySource_polynomial_cost (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : List ZBits) (q : ZBits) (hrn : r.length ≤ v.length) (hmn : mask.length ≤ v.length) :
    (verifySource v r α H K mask p q).2 ≤
      sourceTimePolynomial.eval (totalInputSize v r α H K mask p q) := by
  let L := totalInputSize v r α H K mask p q
  have hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ L := by
    intro x hx
    have h := size_mem_le_sum fractionSize v x hx
    have hw := fractionWidth_le_size x
    dsimp [L,totalInputSize]
    omega
  have hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ L := by
    intro x hx
    have h := size_mem_le_sum fractionSize r x hx
    have hw := fractionWidth_le_size x
    dsimp [L,totalInputSize]
    omega
  have hα : ComplexityTimeFractions.width α ≤ L := by
    have h := fractionWidth_le_size α
    dsimp [L,totalInputSize]
    omega
  have hH : ComplexityTimeFractions.width H ≤ L := by
    have h := fractionWidth_le_size H
    dsimp [L,totalInputSize]
    omega
  have hK : K.length ≤ L := by dsimp [L,totalInputSize]; omega
  have hp : ∀ x ∈ p, ComplexityTimeVerifier.width x ≤ L := by
    intro x hx
    have h := size_mem_le_sum integerSize p x hx
    have hw := integerWidth_le_size x
    dsimp [L,totalInputSize]
    omega
  have hq : ComplexityTimeVerifier.width q ≤ L := by
    have h := integerWidth_le_size q
    dsimp [L,totalInputSize]
    omega
  have hn : v.length ≤ L := by dsimp [L,totalInputSize]; omega
  have hpn : p.length ≤ L := by dsimp [L,totalInputSize]; omega
  have h := verifySource_cost v r α H K mask p q hrn hmn hv hr hα hH hK hp hq
  have hm := sourceBudget_mono hn (le_refl L) (le_refl L) hpn
  rw [sourceTimePolynomial_eval]
  change _ ≤ sourceBudget L L L L+4*L+1
  omega

end BalancedAssortments.ComplexityTimeSourcePipeline
