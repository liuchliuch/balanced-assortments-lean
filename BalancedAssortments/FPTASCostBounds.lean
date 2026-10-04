import BalancedAssortments.FPTASBounds
import BalancedAssortments.PolyhedralBasisCoefficientBounds

/-! Explicit polynomial bounds for the actual outer FPTAS grids and their
rational fields. These size/count theorems do not alone assert machine runtime. -/
namespace BalancedAssortments.FPTASCost
open FPTAS PolyhedralBasis

structure InputBitBound {n : ℕ} (d : Input n) (δ : ℚ) (B : ℕ) : Prop where
  price : ∀ i, CoeffBound B (d.r i)
  attraction : ∀ i, CoeffBound B (d.v i)
  alpha : CoeffBound B d.α
  delta : CoeffBound B δ
  cardinality : CoeffBound B (n+1 : ℚ)

lemma fold_max_bound {B : ℕ} (xs : List ℚ) {a : ℚ} (ha : CoeffBound B a)
    (hx : ∀ x ∈ xs, CoeffBound B x) : CoeffBound B (xs.foldl max a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (ha.max (hx x (by simp)))
    intro y hy
    exact hx y (by simp [hy])

lemma fold_min_bound {B : ℕ} (xs : List ℚ) {a : ℚ} (ha : CoeffBound B a)
    (hx : ∀ x ∈ xs, CoeffBound B x) : CoeffBound B (xs.foldl min a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (ha.min (hx x (by simp)))
    intro y hy
    exact hx y (by simp [hy])

lemma maxList_bound {B : ℕ} (xs : List ℚ) (hx : ∀ x ∈ xs, CoeffBound B x) :
    CoeffBound B (maxList xs) := fold_max_bound xs (CoeffBound.zero B) hx

lemma extrema_bounds {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B) :
    CoeffBound B (vmin d) ∧ CoeffBound B (vmax d) ∧ CoeffBound B (rmax d) := by
  refine ⟨?_, ?_, ?_⟩
  · apply fold_min_bound _ (h.attraction 0)
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact h.attraction i
  · apply maxList_bound
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact h.attraction i
  · apply maxList_bound
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact h.price i

lemma singletonValue_bound {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B) :
    CoeffBound (3*B+1) (singletonValue d) := by
  apply maxList_bound
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  rw [singleton_revenue]
  have hh := (h.price i |>.mul (h.attraction i)).div ((CoeffBound.one 0).add (h.attraction i))
  convert hh using 1 <;> omega

lemma horizon_bound {A C : ℕ} {a cap δ : ℚ} (ha : CoeffBound A a) (hc : CoeffBound C cap) :
    GridBounds.gridHorizon a δ cap ≤ GridBounds.blockLength δ * (A+C+2) := by
  unfold GridBounds.gridHorizon GridBounds.ratioBits
  apply Nat.mul_le_mul_left
  have han := ha.sizes.2
  have hcn := hc.sizes.1
  omega

lemma geometricGrid_length (a δ cap : ℚ) (horizon : ℕ) :
    (Grids.geometricGrid a δ cap horizon).length ≤ horizon+1 := by
  unfold Grids.geometricGrid
  exact (List.length_filter_le _ _).trans_eq (by simp)

lemma grid_member_bound {A B horizon : ℕ} {a δ cap u : ℚ}
    (ha : CoeffBound A a) (hδ : CoeffBound B δ)
    (hu : u ∈ Grids.geometricGrid a δ cap horizon) :
    CoeffBound (A+(B+1)*horizon) u := by
  obtain ⟨j, hj, rfl, _⟩ := Grids.mem_geometricGrid.mp hu
  have hh := ha.mul (((CoeffBound.one 0).add hδ).pow j)
  apply hh.mono
  simp only [Nat.zero_add]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hj) _

/-- Uniform scale/revenue exponent bound; Q=ceil(1/δ) is the precision parameter. -/
def outerHorizon (B Q : ℕ) : ℕ := Q * (8 * (B+1))
def outerWidth (B Q : ℕ) : ℕ := 3*B+1+(B+1)*outerHorizon B Q

theorem scales_bound {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B) :
    (scales d δ).length ≤ outerHorizon B (GridBounds.blockLength δ)+1 ∧
      ∀ τ ∈ scales d δ, CoeffBound (outerWidth B (GridBounds.blockLength δ)) τ := by
  obtain ⟨hmin, hmax, _⟩ := extrema_bounds d δ h
  have hbase : CoeffBound (3*B) (d.α * vmin d / (n+1 : ℚ)) := by
    convert (h.alpha.mul hmin).div h.cardinality using 1 <;> omega
  have hcap := h.alpha.mul hmax
  have hhor : GridBounds.gridHorizon (d.α * vmin d / (n+1 : ℚ)) δ (d.α * vmax d) ≤
      outerHorizon B (GridBounds.blockLength δ) := by
    exact (horizon_bound hbase hcap).trans (Nat.mul_le_mul_left _ (by omega))
  constructor
  · exact (geometricGrid_length _ _ _ _).trans (Nat.add_le_add_right hhor 1)
  · intro τ hτ
    have hh := grid_member_bound hbase h.delta hτ
    apply hh.mono
    unfold outerWidth
    have hi := Nat.mul_le_mul_left (B+1) hhor
    omega

theorem revenues_bound {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B) :
    (revenues d δ).length ≤ outerHorizon B (GridBounds.blockLength δ)+1 ∧
      ∀ ρ ∈ revenues d δ, CoeffBound (outerWidth B (GridBounds.blockLength δ)) ρ := by
  have hbase := singletonValue_bound d δ h
  have hcap := (extrema_bounds d δ h).2.2
  have hhor : GridBounds.gridHorizon (singletonValue d) δ (rmax d) ≤
      outerHorizon B (GridBounds.blockLength δ) := by
    apply (horizon_bound hbase hcap).trans
    unfold outerHorizon
    apply Nat.mul_le_mul_left
    omega
  constructor
  · exact (geometricGrid_length _ _ _ _).trans (Nat.add_le_add_right hhor 1)
  · intro ρ hρ
    have hh := grid_member_bound hbase h.delta hρ
    apply hh.mono
    unfold outerWidth
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hhor) _

end BalancedAssortments.FPTASCost
