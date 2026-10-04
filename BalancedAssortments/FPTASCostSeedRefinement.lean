import BalancedAssortments.FPTASCostOuterSeeds
import BalancedAssortments.FPTASBounds

/-! Direct connection of the bit seed program to the actual FPTAS input fields.
Binary representations may be unreduced and padded; no canonicalization is needed. -/
namespace BalancedAssortments.FPTASCostSeeds
open KnapsackCostRational FPTASCostGrid FPTAS

 theorem outerSeeds_actual {n : ℕ} (d : Input n) (δ : ℚ)
    (alpha delta count : Fraction) (rv : Fin (n+1) → Product)
    (ha : alpha.decode = d.α) (hd : delta.decode = δ) (hc : count.decode = (n+1 : ℚ))
    (hdr : delta.Valid) (hvalid : ∀ i, (rv i).1.Valid ∧ (rv i).2.Valid)
    (hr : ∀ i, (rv i).1.decode = d.r i) (hv : ∀ i, (rv i).2.decode = d.v i) :
    let out := (outerSeeds alpha delta count (rv 0).2 ((List.finRange (n+1)).map rv)).1
    out.scaleBase.decode = d.α * vmin d / (n+1 : ℚ) ∧
    out.scaleCap.decode = d.α * vmax d ∧
    out.revenueBase.decode = singletonValue d ∧
    out.revenueCap.decode = rmax d ∧ out.ratio.decode = 1+δ := by
  let xs := (List.finRange (n+1)).map rv
  have hxs : ∀ p ∈ xs, p.1.Valid ∧ p.2.Valid := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact hvalid i
  have hs := outerSeeds_decode alpha delta count (rv 0).2 xs hdr (hvalid 0).2 hxs
  have hvmap : xs.map (fun p => p.2.decode) = (List.finRange (n+1)).map d.v := by
    simp [xs, List.map_map, hv]
  have hrmap : xs.map (fun p => p.1.decode) = (List.finRange (n+1)).map d.r := by
    simp [xs, List.map_map, hr]
  have hsmap : xs.map (fun p => p.1.decode*p.2.decode/(1+p.2.decode)) =
      (List.finRange (n+1)).map (fun i => revenue d (singleton d i)) := by
    simp [xs, List.map_map, hr, hv, singleton_revenue]
  dsimp only at hs ⊢
  rw [ha, hd, hc, hv 0, hvmap, hrmap, hsmap] at hs
  exact hs

/-- The cost and all output widths for that exact original-input bridge. -/
theorem outerSeeds_actual_cost_width {n b : ℕ}
    (alpha delta count : Fraction) (rv : Fin (n+1) → Product)
    (hb : 1 ≤ b) (ha : alpha.Width b) (hd : delta.Width b) (hc : count.Width b)
    (hw : ∀ i, (rv i).1.Width b ∧ (rv i).2.Width b) :
    let out := outerSeeds alpha delta count (rv 0).2 ((List.finRange (n+1)).map rv)
    out.1.Width (7*b+4) ∧ out.2 ≤ seedCost (n+1) b := by
  have hxs : ∀ p ∈ (List.finRange (n+1)).map rv, p.1.Width b ∧ p.2.Width b := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact hw i
  refine ⟨outerSeeds_width _ _ _ _ _ hb ha hd hc (hw 0).2 hxs, ?_⟩
  simpa using outerSeeds_cost _ _ _ _ _ hb ha hd hc (hw 0).2 hxs

end BalancedAssortments.FPTASCostSeeds
