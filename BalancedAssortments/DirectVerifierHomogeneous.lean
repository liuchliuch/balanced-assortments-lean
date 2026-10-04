import BalancedAssortments.DirectVerifierAlgebra

namespace BalancedAssortments.DirectVerifier
open scoped BigOperators
open DecisionPolyhedron

def RationalLinearFeasible {n : ℕ} (v r : Fin n→ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (w : Fin n→ℚ) : Prop :=
  (∀ i,0≤w i ∧ w i≤v i) ∧ (∑ i,w i/v i)≤K ∧
  (∀ i,i∉A→w i=0) ∧ (∀ i∈A,∀ j∈A,α*w j≤w i) ∧ H≤∑ i,(r i-H)*w i

lemma rationalLinearFeasible_cast {n : ℕ} (v r : Fin n→ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (w : Fin n→ℚ) :
    LinearFeasible v r α H K A (fun i => (w i : ℝ)) ↔ RationalLinearFeasible v r α H K A w := by
  unfold LinearFeasible RationalLinearFeasible
  dsimp only
  norm_cast

/-- Homogeneous witness inequalities. All terms can be checked with signed
integer products/sums after clearing positive input denominators. -/
def Homogeneous {n : ℕ} (v r : Fin n→ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ) : Prop :=
  (∀ i,0≤p i ∧ (p i : ℚ)≤q*v i) ∧
  (∑ i,(p i : ℚ)/v i)≤K*(q : ℚ) ∧
  (∀ i,i∉A→p i=0) ∧ (∀ i∈A,∀ j∈A,α*(p j : ℚ)≤p i) ∧
  H*((q : ℚ)+∑ i,(p i : ℚ))≤∑ i,r i*(p i : ℚ)

theorem homogeneous_iff_linear {n : ℕ} (v r : Fin n→ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ) (hq : 0<q) :
    Homogeneous v r α H K A p q ↔
      LinearFeasible v r α H K A (fun i => (p i : ℝ)/(q : ℝ)) := by
  have hqQ : (0 : ℚ)<q := by exact_mod_cast hq
  have hqne : (q : ℚ)≠0 := ne_of_gt hqQ
  let w : Fin n→ℚ := fun i => (p i : ℚ)/(q : ℚ)
  have hc : (fun i => (p i : ℝ)/(q : ℝ))=(fun i => (w i : ℝ)) := by
    funext i;simp [w]
  rw [hc,rationalLinearFeasible_cast]
  dsimp only [w]
  have hnonneg (i : Fin n) : 0≤(p i : ℚ)/(q : ℚ) ↔ 0≤p i := by
    rw [le_div_iff₀ hqQ]
    simp only [zero_mul]
    exact_mod_cast Iff.rfl
  have hcap (i : Fin n) : (p i : ℚ)/(q : ℚ)≤v i ↔ (p i : ℚ)≤q*v i := by
    rw [div_le_iff₀ hqQ,mul_comm (v i)]
  have hzero (i : Fin n) : (p i : ℚ)/(q : ℚ)=0 ↔ p i=0 := by simp [hqne,ne_of_gt hq]
  have hbal (i j : Fin n) : α*((p j : ℚ)/(q : ℚ))≤(p i : ℚ)/(q : ℚ) ↔ α*(p j : ℚ)≤p i := by
    rw [← mul_div_assoc,div_le_div_iff_of_pos_right hqQ]
  have hrank : (∑ i,((p i : ℚ)/(q : ℚ))/v i)= (∑ i,(p i : ℚ)/v i)/(q : ℚ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htarget : (H≤∑ i,(r i-H)*((p i : ℚ)/(q : ℚ))) ↔
      H*((q : ℚ)+∑ i,(p i : ℚ))≤∑ i,r i*(p i : ℚ) := by
    have he : (∑ i,(r i-H)*((p i : ℚ)/(q : ℚ)))=
        ((∑ i,r i*(p i : ℚ))-H*(∑ i,(p i : ℚ)))/(q : ℚ) := by
      calc
        _ = (∑ i,(r i-H)*(p i : ℚ))/(q : ℚ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by simp [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    rw [he,le_div_iff₀ hqQ]
    constructor <;> intro h <;> nlinarith
  unfold Homogeneous RationalLinearFeasible
  simp only [hnonneg,hcap,hzero,hbal,hrank,div_le_iff₀ hqQ,htarget]

end BalancedAssortments.DirectVerifier
