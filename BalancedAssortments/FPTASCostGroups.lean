import BalancedAssortments.FPTASCostOptions
import BalancedAssortments.FPTAS

namespace BalancedAssortments.FPTASCostOptions
open KnapsackCostRational FPTASCostGrid FPTASCostSeeds

def groupsBits : ℕ → Fraction → Fraction → Fraction → Fraction → List (Fraction × Fraction) →
    List (List KnapsackCostState.Item) × ℕ
  | _,_,_,_,_,[] => ([],1)
  | H,τ,ratio,α,ρ,(r,v)::rest =>
      let group := groupBits H τ ratio α v r ρ
      let tail := groupsBits H τ ratio α ρ rest
      (group.1::tail.1,group.2+tail.2+4)

lemma groupsBits_eq (H : ℕ) (τ ratio α ρ : Fraction) (products : List (Fraction × Fraction)) :
    (groupsBits H τ ratio α ρ products).1 = products.map
      (fun rv => (groupBits H τ ratio α rv.2 rv.1 ρ).1) := by
  induction products with
  | nil => rfl
  | cons rv rest ih => cases rv; simp [groupsBits,ih]

lemma groupsBits_cost (H : ℕ) (τ ratio α ρ : Fraction) (products : List (Fraction × Fraction))
    {b : ℕ} (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b) (hp : ρ.Width b)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    (groupsBits H τ ratio α ρ products).2 ≤ products.length*(groupCost H b+4)+1 := by
  induction products with
  | nil => simp [groupsBits]
  | cons rv rest ih =>
    obtain ⟨r,v⟩ := rv
    have hw := hprod (r,v) (by simp)
    have hh := groupBits_cost H τ ratio α v r ρ ht hratio ha hw.2 hw.1 hp
    have ht' := ih (fun rv hrv => hprod rv (by simp [hrv]))
    simp only [groupsBits,List.length_cons]
    nlinarith

/-- Coordinatewise exact refinement of a complete generated option family. -/
theorem groupsBits_decode {n : ℕ} (d : FPTAS.Input n) (H : ℕ) (τ ratio α ρ : Fraction)
    (rv : Fin (n+1) → Fraction × Fraction) (δ : ℚ)
    (ht : τ.Valid) (hratio : ratio.Valid) (ha : α.Valid) (hp : ρ.Valid)
    (hprod : ∀ i, (rv i).1.Valid ∧ (rv i).2.Valid)
    (hdecode : ∀ i, (rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (halpha : α.decode = d.α) (hrat : ratio.decode = 1+δ)
    (htpos : 0 < τ.decode) (hapos : 0 < d.α) (hvpos : ∀ i, 0 < d.v i) (hd : 0 < δ)
    (hcover : ∀ i, min (d.v i) (τ.decode/d.α) < τ.decode*(1+δ)^(H+1)) :
    ((groupsBits H τ ratio α ρ ((List.finRange (n+1)).map rv)).1.map
      (List.map KnapsackCostState.Item.decode)) = FPTAS.groups d δ τ.decode ρ.decode := by
  rw [groupsBits_eq,List.map_map,List.map_map]
  unfold FPTAS.groups
  apply List.map_congr_left
  intro i _
  have hh := groupBits_decode H τ ratio α (rv i).2 (rv i).1 ρ δ ht hratio ha
    (hprod i).2 (hprod i).1 hp htpos (by rwa [halpha]) (by simpa only [(hdecode i).2] using hvpos i) hd hrat
    (by simpa only [halpha,(hdecode i).2] using hcover i)
  simpa only [Function.comp_apply,FPTAS.group,halpha,(hdecode i).1,(hdecode i).2] using hh

theorem groupsBits_width (H : ℕ) (τ ratio α ρ : Fraction) (products : List (Fraction × Fraction))
    {b : ℕ} (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b) (hp : ρ.Width b)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    ∀ g ∈ (groupsBits H τ ratio α ρ products).1,
      g.length ≤ H+2 ∧ ∀ i ∈ g, i.Width (groupWidth H b) := by
  intro g hg
  rw [groupsBits_eq] at hg
  obtain ⟨rv,hrv,rfl⟩ := List.mem_map.mp hg
  exact ⟨groupBits_length _ _ _ _ _ _ _,
    groupBits_width _ _ _ _ _ _ _ ht hratio ha (hprod rv hrv).2 (hprod rv hrv).1 hp⟩

theorem groupsBits_valid (H : ℕ) (τ ratio α ρ : Fraction) (products : List (Fraction × Fraction))
    (ht : τ.Valid) (hratio : ratio.Valid) (hp : ρ.Valid)
    (hapos : 0 < α.decode)
    (hprod : ∀ rv ∈ products, rv.1.Valid ∧ 0 < rv.2.decode) :
    ∀ g ∈ (groupsBits H τ ratio α ρ products).1, ∀ i ∈ g, i.Valid := by
  intro g hg
  rw [groupsBits_eq] at hg
  obtain ⟨rv,hrv,rfl⟩ := List.mem_map.mp hg
  exact groupBits_valid _ _ _ _ _ _ _ ht hratio (hprod rv hrv).1 hp hapos (hprod rv hrv).2

end BalancedAssortments.FPTASCostOptions
