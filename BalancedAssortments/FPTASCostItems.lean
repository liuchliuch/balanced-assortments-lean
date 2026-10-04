import BalancedAssortments.FPTASCostBounds
import BalancedAssortments.KnapsackCostEncoding

/-! Uniform polynomial-sized exact option and DP scale fields for the actual
outer grid routine. Bounds are polynomials in original coefficient bits B and
Q=ceil(1/δ), without a supplied option or profit-size oracle. -/
namespace BalancedAssortments.FPTASCost
open FPTAS PolyhedralBasis

def innerHorizon (B Q : ℕ) : ℕ := Q * (2 * outerWidth B Q + B + 2)
def valueWidth (B Q : ℕ) : ℕ := outerWidth B Q + (B+1) * innerHorizon B Q
def profitWidth (B Q : ℕ) : ℕ := B + outerWidth B Q + 1 + valueWidth B Q
def itemWidth (B Q : ℕ) : ℕ := profitWidth B Q + 2*B + 1

lemma option_horizon_bound {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B)
    {τ : ℚ} (hτ : CoeffBound (outerWidth B (GridBounds.blockLength δ)) τ) (i : Fin (n+1)) :
    GridBounds.gridHorizon τ δ (min (d.v i) (τ/d.α)) ≤ innerHorizon B (GridBounds.blockLength δ) := by
  have hv : CoeffBound (outerWidth B (GridBounds.blockLength δ)+B) (d.v i) :=
    (h.attraction i).mono (by omega)
  have hcap := hv.min (hτ.div h.alpha)
  apply (horizon_bound hτ hcap).trans
  unfold innerHorizon
  apply Nat.mul_le_mul_left
  omega

/-- Every group has only polynomially many options, including zero; every value,
weight and transformed profit has the stated explicit bit-magnitude bound. -/
theorem group_bounds {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B)
    {τ ρ : ℚ} (hτ : τ ∈ scales d δ) (hρ : ρ ∈ revenues d δ) (i : Fin (n+1)) :
    (group d δ τ ρ i).length ≤ innerHorizon B (GridBounds.blockLength δ)+2 ∧
    ∀ it ∈ group d δ τ ρ i,
      CoeffBound (valueWidth B (GridBounds.blockLength δ)) it.value ∧
      CoeffBound (valueWidth B (GridBounds.blockLength δ)+B) it.weight ∧
      CoeffBound (profitWidth B (GridBounds.blockLength δ)) it.profit := by
  have ht := (scales_bound d δ h).2 τ hτ
  have hr := (revenues_bound d δ h).2 ρ hρ
  have hhor := option_horizon_bound d δ h ht i
  constructor
  · simp only [group, List.length_cons, List.length_map]
    have hg := geometricGrid_length τ δ (min (d.v i) (τ/d.α))
      (GridBounds.gridHorizon τ δ (min (d.v i) (τ/d.α)))
    have hf := List.length_filter_le
      (fun u : ℚ => decide (0 < (d.r i - ρ)*u))
      (Grids.geometricGrid τ δ (min (d.v i) (τ/d.α))
        (GridBounds.gridHorizon τ δ (min (d.v i) (τ/d.α))))
    omega
  · intro it hit
    simp only [group, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at hit
    rcases hit with rfl | ⟨u, ⟨hu, _⟩, rfl⟩
    · exact ⟨CoeffBound.zero _, CoeffBound.zero _, CoeffBound.zero _⟩
    · have hu' : CoeffBound (valueWidth B (GridBounds.blockLength δ)) u := by
        apply (grid_member_bound ht h.delta hu).mono
        unfold valueWidth
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hhor) _
      exact ⟨hu', hu'.div (h.attraction i), (h.price i |>.sub hr).mul hu'⟩

lemma groups_length {n : ℕ} (d : Input n) (δ τ ρ : ℚ) :
    (groups d δ τ ρ).length = n+1 := by simp [groups]

lemma maxProfit_bound_bits {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B)
    {τ ρ : ℚ} (hτ : τ ∈ scales d δ) (hρ : ρ ∈ revenues d δ) :
    CoeffBound (profitWidth B (GridBounds.blockLength δ))
      (maxList (((groups d δ τ ρ).flatten).map Knapsack.Item.profit)) := by
  apply maxList_bound
  intro x hx
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
  obtain ⟨g, hg, hi⟩ := List.mem_flatten.mp hit
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact ((group_bounds d δ h hτ hρ i).2 it hi).2.2

/-- Canonical field encoding widths for every actual DP call. The scale θ is
also bounded, including the degenerate zero-maxProfit case. -/
theorem call_field_widths {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B)
    {τ ρ : ℚ} (hτ : τ ∈ scales d δ) (hρ : ρ ∈ revenues d δ) :
    (KnapsackCostRational.encode
      (δ * maxList (((groups d δ τ ρ).flatten).map Knapsack.Item.profit) / (n+1))).Width
        (itemWidth B (GridBounds.blockLength δ)) ∧
    ∀ g ∈ groups d δ τ ρ, ∀ it ∈ g,
      (KnapsackCostRational.encode it.value).Width (itemWidth B (GridBounds.blockLength δ)) ∧
      (KnapsackCostRational.encode it.weight).Width (itemWidth B (GridBounds.blockLength δ)) ∧
      (KnapsackCostRational.encode it.profit).Width (itemWidth B (GridBounds.blockLength δ)) := by
  have hm := maxProfit_bound_bits d δ h hτ hρ
  constructor
  · have ht := (h.delta.mul hm).div h.cardinality
    have hs := ht.sizes
    apply KnapsackCostRational.encode_width
    · convert hs.1 using 1 <;> unfold itemWidth <;> omega
    · convert hs.2 using 1 <;> unfold itemWidth <;> omega
  · intro g hg it hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hv, hw, hp⟩ := (group_bounds d δ h hτ hρ i).2 it hi
    have hvm : valueWidth B (GridBounds.blockLength δ)+1 ≤ itemWidth B (GridBounds.blockLength δ) := by
      unfold itemWidth profitWidth; omega
    have hwm : valueWidth B (GridBounds.blockLength δ)+B+1 ≤ itemWidth B (GridBounds.blockLength δ) := by
      unfold itemWidth profitWidth; omega
    have hpm : profitWidth B (GridBounds.blockLength δ)+1 ≤ itemWidth B (GridBounds.blockLength δ) := by
      unfold itemWidth; omega
    refine ⟨KnapsackCostRational.encode_width (hv.sizes.1.trans hvm) (hv.sizes.2.trans hvm),
      KnapsackCostRational.encode_width (hw.sizes.1.trans hwm) (hw.sizes.2.trans hwm),
      KnapsackCostRational.encode_width (hp.sizes.1.trans hpm) (hp.sizes.2.trans hpm)⟩

end BalancedAssortments.FPTASCost
