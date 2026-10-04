import BalancedAssortments.FixedSupportCostCertified
import BalancedAssortments.NPCNFEncoding

/-! Original stored-input-volume specialization of the exact-support solver.
The volume counts all signed numerator and denominator bits and product records;
no caller-selected uniform width parameter remains. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostPoints
open FixedSupportCostOrder FixedSupportCostScale FixedSupportCostScaleList
open FixedSupportCostScalars FixedSupportCostEvaluate FixedSupportCostVector

def fractionVolume (x : Fraction) : ℕ := x.num.1.length+x.num.2.length+x.den.length
def inputVolume {I : Type*} (α K : Fraction) (ps : List (I×Product)) : ℕ :=
  1+ps.length+fractionVolume α+fractionVolume K+
    (ps.map (fun p => fractionVolume p.2.1+fractionVolume p.2.2)).sum

lemma width_le_volume (x : Fraction) : width x ≤ fractionVolume x := by
  simp only [width,ComplexityTimeVerifier.width,fractionVolume]
  omega
lemma member_le_sum {xs : List ℕ} {x : ℕ} (h : x∈xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · have hh := ih h;simp only [List.sum_cons];omega

lemma inputVolume_bounds {I : Type*} (α K : Fraction) (ps : List (I×Product)) :
    ps.length ≤ inputVolume α K ps ∧ width α ≤ inputVolume α K ps ∧
      width K ≤ inputVolume α K ps ∧ ∀ p∈ps,p.2.Width (inputVolume α K ps) := by
  have ha := width_le_volume α
  have hk := width_le_volume K
  refine ⟨by unfold inputVolume;omega,by unfold inputVolume;omega,by unfold inputVolume;omega,?_⟩
  intro p hp
  have hh := member_le_sum (List.mem_map.mpr ⟨p,hp,rfl⟩ : fractionVolume p.2.1+fractionVolume p.2.2∈ps.map (fun p => fractionVolume p.2.1+fractionVolume p.2.2))
  have h1 := width_le_volume p.2.1
  have h2 := width_le_volume p.2.2
  constructor <;> unfold inputVolume <;> omega

/-- The product labels are positions, not arbitrary binary integers; their
record count is charged by inputVolume and the solver only transports them. -/
theorem runBits_input_cost {I : Type*} (α K : Fraction) (ps : List (I×Product))
    (ha : Valid α) (hk : Valid K) (hp : ∀ p∈ps,p.2.Valid) :
    (runBits α K ps).2 ≤ runCost ps.length (inputVolume α K ps) := by
  have hb := inputVolume_bounds α K ps
  exact runBits_cost α K ps ha hk hp hb.2.1 hb.2.2.1 hb.2.2.2

private def NatPoly (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ,∀ n,f n=p.eval n
private lemma poly_c (a : ℕ) : NatPoly (fun _ => a) := ⟨Polynomial.C a,by simp⟩
private lemma poly_x : NatPoly (fun n => n) := ⟨Polynomial.X,by simp⟩
private lemma poly_add {f g : ℕ → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun n => f n+g n) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg;exact ⟨p+q,by intro n;simp [hp,hq]⟩
private lemma poly_mul {f g : ℕ → ℕ} (hf : NatPoly f) (hg : NatPoly g) : NatPoly (fun n => f n*g n) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg;exact ⟨p*q,by intro n;simp [hp,hq]⟩
private lemma poly_pow {f : ℕ → ℕ} (k : ℕ) (hf : NatPoly f) : NatPoly (fun n => (f n)^k) := by
  obtain ⟨p,hp⟩ := hf;exact ⟨p^k,by intro n;simp [hp]⟩

@[gcongr] private lemma budget_inverseWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : inverseWidth x0 x1 ≤ inverseWidth y0 y1 := by
  unfold inverseWidth
  gcongr

private lemma budget_inverseWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => inverseWidth (f0 n) (f1 n)) := by
  dsimp only [inverseWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow

@[gcongr] private lemma budget_inverseCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : inverseCost x0 x1 ≤ inverseCost y0 y1 := by
  unfold inverseCost
  gcongr

private lemma budget_inverseCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => inverseCost (f0 n) (f1 n)) := by
  dsimp only [inverseCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly

@[gcongr] private lemma budget_upperWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : upperWidth x0 x1 ≤ upperWidth y0 y1 := by
  unfold upperWidth
  gcongr

private lemma budget_upperWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => upperWidth (f0 n) (f1 n)) := by
  dsimp only [upperWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly

@[gcongr] private lemma budget_upperCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : upperCost x0 x1 ≤ upperCost y0 y1 := by
  unfold upperCost
  gcongr

private lemma budget_upperCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => upperCost (f0 n) (f1 n)) := by
  dsimp only [upperCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly

@[gcongr] private lemma budget_cutsCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : cutsCost x0 x1 ≤ cutsCost y0 y1 := by
  unfold cutsCost
  gcongr

private lemma budget_cutsCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => cutsCost (f0 n) (f1 n)) := by
  dsimp only [cutsCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly

@[gcongr] private lemma budget_rootTopWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : rootTopWidth x0 x1 ≤ rootTopWidth y0 y1 := by
  unfold rootTopWidth
  gcongr

private lemma budget_rootTopWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => rootTopWidth (f0 n) (f1 n)) := by
  dsimp only [rootTopWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly

@[gcongr] private lemma budget_rootBottomWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : rootBottomWidth x0 x1 ≤ rootBottomWidth y0 y1 := by
  unfold rootBottomWidth
  gcongr

private lemma budget_rootBottomWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => rootBottomWidth (f0 n) (f1 n)) := by
  dsimp only [rootBottomWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly

@[gcongr] private lemma budget_rootWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : rootWidth x0 x1 ≤ rootWidth y0 y1 := by
  unfold rootWidth
  gcongr

private lemma budget_rootWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => rootWidth (f0 n) (f1 n)) := by
  dsimp only [rootWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly

@[gcongr] private lemma budget_rootCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : rootCost x0 x1 ≤ rootCost y0 y1 := by
  unfold rootCost
  gcongr

private lemma budget_rootCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => rootCost (f0 n) (f1 n)) := by
  dsimp only [rootCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly

@[gcongr] private lemma budget_scaleCutWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : scaleCutWidth x0 x1 ≤ scaleCutWidth y0 y1 := by
  unfold scaleCutWidth
  gcongr

private lemma budget_scaleCutWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => scaleCutWidth (f0 n) (f1 n)) := by
  dsimp only [scaleCutWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly

@[gcongr] private lemma budget_scaleRootWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : scaleRootWidth x0 x1 ≤ scaleRootWidth y0 y1 := by
  unfold scaleRootWidth
  gcongr

private lemma budget_scaleRootWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => scaleRootWidth (f0 n) (f1 n)) := by
  dsimp only [scaleRootWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly

@[gcongr] private lemma budget_scaleWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : scaleWidth x0 x1 ≤ scaleWidth y0 y1 := by
  unfold scaleWidth
  gcongr

private lemma budget_scaleWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => scaleWidth (f0 n) (f1 n)) := by
  dsimp only [scaleWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly

@[gcongr] private lemma budget_scaleCount_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) : scaleCount x0 ≤ scaleCount y0 := by
  unfold scaleCount
  gcongr

private lemma budget_scaleCount_poly {f0 : ℕ → ℕ} (h0 : NatPoly f0) : NatPoly (fun n => scaleCount (f0 n)) := by
  dsimp only [scaleCount]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly

@[gcongr] private lemma budget_scaleCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : scaleCost x0 x1 ≤ scaleCost y0 y1 := by
  unfold scaleCost
  gcongr

private lemma budget_scaleCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => scaleCost (f0 n) (f1 n)) := by
  dsimp only [scaleCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly

@[gcongr] private lemma budget_primitiveCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) : primitiveCost x0 ≤ primitiveCost y0 := by
  unfold primitiveCost
  gcongr

private lemma budget_primitiveCost_poly {f0 : ℕ → ℕ} (h0 : NatPoly f0) : NatPoly (fun n => primitiveCost (f0 n)) := by
  dsimp only [primitiveCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly

@[gcongr] private lemma budget_capCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : capCost x0 x1 ≤ capCost y0 y1 := by
  unfold capCost
  gcongr

private lemma budget_capCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => capCost (f0 n) (f1 n)) := by
  dsimp only [capCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly

@[gcongr] private lemma budget_budgetCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : budgetCost x0 x1 x2 ≤ budgetCost y0 y1 y2 := by
  unfold budgetCost
  gcongr

private lemma budget_budgetCost_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => budgetCost (f0 n) (f1 n) (f2 n)) := by
  dsimp only [budgetCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly

@[gcongr] private lemma budget_itemWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) : itemWidth x0 ≤ itemWidth y0 := by
  unfold itemWidth
  gcongr

private lemma budget_itemWidth_poly {f0 : ℕ → ℕ} (h0 : NatPoly f0) : NatPoly (fun n => itemWidth (f0 n)) := by
  dsimp only [itemWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly

@[gcongr] private lemma budget_budgetWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : budgetWidth x0 x1 ≤ budgetWidth y0 y1 := by
  unfold budgetWidth
  gcongr

private lemma budget_budgetWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => budgetWidth (f0 n) (f1 n)) := by
  dsimp only [budgetWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly

@[gcongr] private lemma budget_allocationWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : allocationWidth x0 x1 ≤ allocationWidth y0 y1 := by
  unfold allocationWidth
  gcongr

private lemma budget_allocationWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => allocationWidth (f0 n) (f1 n)) := by
  dsimp only [allocationWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly

@[gcongr] private lemma budget_vectorWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : vectorWidth x0 x1 ≤ vectorWidth y0 y1 := by
  unfold vectorWidth
  gcongr

private lemma budget_vectorWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => vectorWidth (f0 n) (f1 n)) := by
  dsimp only [vectorWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly

@[gcongr] private lemma budget_coordinateCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : coordinateCost x0 x1 x2 ≤ coordinateCost y0 y1 y2 := by
  unfold coordinateCost
  gcongr

private lemma budget_coordinateCost_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => coordinateCost (f0 n) (f1 n) (f2 n)) := by
  dsimp only [coordinateCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly

@[gcongr] private lemma budget_numeratorWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : numeratorWidth x0 x1 x2 ≤ numeratorWidth y0 y1 y2 := by
  unfold numeratorWidth
  gcongr

private lemma budget_numeratorWidth_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => numeratorWidth (f0 n) (f1 n) (f2 n)) := by
  dsimp only [numeratorWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly

@[gcongr] private lemma budget_denominatorWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : denominatorWidth x0 x1 ≤ denominatorWidth y0 y1 := by
  unfold denominatorWidth
  gcongr

private lemma budget_denominatorWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => denominatorWidth (f0 n) (f1 n)) := by
  dsimp only [denominatorWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly

@[gcongr] private lemma budget_objectiveWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : objectiveWidth x0 x1 x2 ≤ objectiveWidth y0 y1 y2 := by
  unfold objectiveWidth
  gcongr

private lemma budget_objectiveWidth_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => objectiveWidth (f0 n) (f1 n) (f2 n)) := by
  dsimp only [objectiveWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly

@[gcongr] private lemma budget_objectiveCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : objectiveCost x0 x1 x2 ≤ objectiveCost y0 y1 y2 := by
  unfold objectiveCost
  gcongr

private lemma budget_objectiveCost_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => objectiveCost (f0 n) (f1 n) (f2 n)) := by
  dsimp only [objectiveCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly

@[gcongr] private lemma budget_evaluationCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : evaluationCost x0 x1 ≤ evaluationCost y0 y1 := by
  unfold evaluationCost
  gcongr

private lemma budget_evaluationCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => evaluationCost (f0 n) (f1 n)) := by
  dsimp only [evaluationCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly

@[gcongr] private lemma budget_pointCount_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) : pointCount x0 ≤ pointCount y0 := by
  unfold pointCount
  gcongr

private lemma budget_pointCount_poly {f0 : ℕ → ℕ} (h0 : NatPoly f0) : NatPoly (fun n => pointCount (f0 n)) := by
  dsimp only [pointCount]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly

@[gcongr] private lemma budget_criticalCostBudget_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : criticalCostBudget x0 x1 ≤ criticalCostBudget y0 y1 := by
  unfold criticalCostBudget
  gcongr

private lemma budget_criticalCostBudget_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => criticalCostBudget (f0 n) (f1 n)) := by
  dsimp only [criticalCostBudget]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly

@[gcongr] private lemma budget_scoreCostBudget_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : scoreCostBudget x0 x1 ≤ scoreCostBudget y0 y1 := by
  unfold scoreCostBudget
  gcongr

private lemma budget_scoreCostBudget_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => scoreCostBudget (f0 n) (f1 n)) := by
  dsimp only [scoreCostBudget]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly

@[gcongr] private lemma budget_orderCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : orderCost x0 x1 x2 ≤ orderCost y0 y1 y2 := by
  unfold orderCost
  gcongr

private lemma budget_orderCost_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => orderCost (f0 n) (f1 n) (f2 n)) := by
  dsimp only [orderCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly

@[gcongr] private lemma budget_patternWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : patternWidth x0 x1 x2 ≤ patternWidth y0 y1 y2 := by
  unfold patternWidth
  gcongr

private lemma budget_patternWidth_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => patternWidth (f0 n) (f1 n) (f2 n)) := by
  dsimp only [patternWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly

@[gcongr] private lemma budget_patternVectorWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : patternVectorWidth x0 x1 x2 ≤ patternVectorWidth y0 y1 y2 := by
  unfold patternVectorWidth
  gcongr

private lemma budget_patternVectorWidth_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => patternVectorWidth (f0 n) (f1 n) (f2 n)) := by
  dsimp only [patternVectorWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly

@[gcongr] private lemma budget_patternObjectiveWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : patternObjectiveWidth x0 x1 x2 ≤ patternObjectiveWidth y0 y1 y2 := by
  unfold patternObjectiveWidth
  gcongr

private lemma budget_patternObjectiveWidth_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => patternObjectiveWidth (f0 n) (f1 n) (f2 n)) := by
  dsimp only [patternObjectiveWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly

@[gcongr] private lemma budget_patternCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) {x2 y2 : ℕ} (h2 : x2 ≤ y2) : patternCost x0 x1 x2 ≤ patternCost y0 y1 y2 := by
  unfold patternCost
  gcongr

private lemma budget_patternCost_poly {f0 f1 f2 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) (h2 : NatPoly f2) : NatPoly (fun n => patternCost (f0 n) (f1 n) (f2 n)) := by
  dsimp only [patternCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly | apply budget_patternObjectiveWidth_poly

@[gcongr] private lemma budget_scoreCount_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) : scoreCount x0 ≤ scoreCount y0 := by
  unfold scoreCount
  gcongr

private lemma budget_scoreCount_poly {f0 : ℕ → ℕ} (h0 : NatPoly f0) : NatPoly (fun n => scoreCount (f0 n)) := by
  dsimp only [scoreCount]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly | apply budget_patternObjectiveWidth_poly | apply budget_patternCost_poly

@[gcongr] private lemma budget_candidateCount_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) : candidateCount x0 ≤ candidateCount y0 := by
  unfold candidateCount
  gcongr

private lemma budget_candidateCount_poly {f0 : ℕ → ℕ} (h0 : NatPoly f0) : NatPoly (fun n => candidateCount (f0 n)) := by
  dsimp only [candidateCount]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly | apply budget_patternObjectiveWidth_poly | apply budget_patternCost_poly | apply budget_scoreCount_poly

@[gcongr] private lemma budget_candidateCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : candidateCost x0 x1 ≤ candidateCost y0 y1 := by
  unfold candidateCost
  gcongr

private lemma budget_candidateCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => candidateCost (f0 n) (f1 n)) := by
  dsimp only [candidateCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly | apply budget_patternObjectiveWidth_poly | apply budget_patternCost_poly | apply budget_scoreCount_poly | apply budget_candidateCount_poly

@[gcongr] private lemma budget_outputObjectiveWidth_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : outputObjectiveWidth x0 x1 ≤ outputObjectiveWidth y0 y1 := by
  unfold outputObjectiveWidth
  gcongr

private lemma budget_outputObjectiveWidth_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => outputObjectiveWidth (f0 n) (f1 n)) := by
  dsimp only [outputObjectiveWidth]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly | apply budget_patternObjectiveWidth_poly | apply budget_patternCost_poly | apply budget_scoreCount_poly | apply budget_candidateCount_poly | apply budget_candidateCost_poly

@[gcongr] private lemma budget_runCost_mono {x0 y0 : ℕ} (h0 : x0 ≤ y0) {x1 y1 : ℕ} (h1 : x1 ≤ y1) : runCost x0 x1 ≤ runCost y0 y1 := by
  unfold runCost
  gcongr

private lemma budget_runCost_poly {f0 f1 : ℕ → ℕ} (h0 : NatPoly f0) (h1 : NatPoly f1) : NatPoly (fun n => runCost (f0 n) (f1 n)) := by
  dsimp only [runCost]
  with_reducible repeat first | assumption | exact poly_x | exact poly_c _ | apply poly_add | apply poly_mul | apply poly_pow | apply budget_inverseWidth_poly | apply budget_inverseCost_poly | apply budget_upperWidth_poly | apply budget_upperCost_poly | apply budget_cutsCost_poly | apply budget_rootTopWidth_poly | apply budget_rootBottomWidth_poly | apply budget_rootWidth_poly | apply budget_rootCost_poly | apply budget_scaleCutWidth_poly | apply budget_scaleRootWidth_poly | apply budget_scaleWidth_poly | apply budget_scaleCount_poly | apply budget_scaleCost_poly | apply budget_primitiveCost_poly | apply budget_capCost_poly | apply budget_budgetCost_poly | apply budget_itemWidth_poly | apply budget_budgetWidth_poly | apply budget_allocationWidth_poly | apply budget_vectorWidth_poly | apply budget_coordinateCost_poly | apply budget_numeratorWidth_poly | apply budget_denominatorWidth_poly | apply budget_objectiveWidth_poly | apply budget_objectiveCost_poly | apply budget_evaluationCost_poly | apply budget_pointCount_poly | apply budget_criticalCostBudget_poly | apply budget_scoreCostBudget_poly | apply budget_orderCost_poly | apply budget_patternWidth_poly | apply budget_patternVectorWidth_poly | apply budget_patternObjectiveWidth_poly | apply budget_patternCost_poly | apply budget_scoreCount_poly | apply budget_candidateCount_poly | apply budget_candidateCost_poly | apply budget_outputObjectiveWidth_poly

lemma runCost_mono_count {n m B : ℕ} (h : n ≤ m) : runCost n B ≤ runCost m B := budget_runCost_mono h le_rfl

lemma runCost_mono_width {n A B : ℕ} (h : A ≤ B) : runCost n A ≤ runCost n B := budget_runCost_mono le_rfl h

lemma runCost_polynomial : ∃ p : Polynomial ℕ,∀ I,runCost I I=p.eval I := budget_runCost_poly poly_x poly_x

/-- A single fixed natural polynomial bounds the full executed solver from its
original stored input alone, without any supplied coefficient-width bound. -/
theorem runBits_polynomial_input : ∃ P : Polynomial ℕ,∀ {I : Type*}
    (α K : Fraction) (ps : List (I×Product)),Valid α → Valid K → (∀ p∈ps,p.2.Valid) →
      (runBits α K ps).2 ≤ P.eval (inputVolume α K ps) := by
  obtain ⟨P,hP⟩ := runCost_polynomial
  refine ⟨P,?_⟩
  intro I α K ps ha hk hp
  rw [← hP]
  exact (runBits_input_cost α K ps ha hk hp).trans (runCost_mono_count (inputVolume_bounds α K ps).1)

end BalancedAssortments.FixedSupportCostProgram
