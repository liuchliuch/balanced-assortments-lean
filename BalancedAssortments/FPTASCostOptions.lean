import BalancedAssortments.FPTASCostSeeds
import BalancedAssortments.KnapsackCostPreprocess
import BalancedAssortments.GridHorizonInvariant

namespace BalancedAssortments.FPTASCostOptions
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid FPTASCostSeeds

/-- Saturating subtraction on nonnegative fractions. It is exact subtraction
whenever y≤x, which is checked before constructing transformed profits. -/
def subtract (x y : Fraction) : Fraction × ℕ :=
  let a := mulBits x.numerator y.denominator
  let b := mulBits y.numerator x.denominator
  let c := Decomposition.CostBinary.subBits a.1 b.1
  let d := mulBits x.denominator y.denominator
  (⟨c.1,d.1⟩, a.2+b.2+c.2+d.2+8)

lemma subtract_valid {x y : Fraction} (hx : x.Valid) (hy : y.Valid) : (subtract x y).1.Valid := by
  simpa only [subtract, Fraction.Valid, mulBits_value] using Nat.mul_pos hx hy

lemma subtract_decode {x y : Fraction} (hx : x.Valid) (hy : y.Valid) (hle : y.decode ≤ x.decode) :
    (subtract x y).1.decode = x.decode-y.decode := by
  have hxq : (0:ℚ) < value x.denominator := by exact_mod_cast hx
  have hyq : (0:ℚ) < value y.denominator := by exact_mod_cast hy
  have hh := (div_le_div_iff₀ hyq hxq).mp hle
  have hn : value y.numerator * value x.denominator ≤ value x.numerator * value y.denominator := by
    exact_mod_cast hh
  simp only [subtract, Fraction.decode, Decomposition.CostBinary.subBits_value, mulBits_value,
    Nat.cast_sub hn, Nat.cast_mul]
  field_simp

lemma subtract_width {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (subtract x y).1.Width (3*b) := by
  have ha := mulBits_length x.numerator y.denominator
  have hb := mulBits_length y.numerator x.denominator
  have hd := mulBits_length x.denominator y.denominator
  have hc := Decomposition.CostBinary.subBits_length
    (mulBits x.numerator y.denominator).1 (mulBits y.numerator x.denominator).1
  have hx1 := hx.1; have hx2 := hx.2; have hy1 := hy.1; have hy2 := hy.2
  constructor <;> simp only [subtract] <;> omega

lemma subtract_cost {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (subtract x y).2 ≤ 1024*(b+1)^2 := by
  have ha := mulBits_cost x.numerator y.denominator
  have hb := mulBits_cost y.numerator x.denominator
  have hd := mulBits_cost x.denominator y.denominator
  have la := mulBits_length x.numerator y.denominator
  have lb := mulBits_length y.numerator x.denominator
  have hc := Decomposition.CostBinary.subBits_cost
    (mulBits x.numerator y.denominator).1 (mulBits y.numerator x.denominator).1
  have hx1 := hx.1; have hx2 := hx.2; have hy1 := hy.1; have hy2 := hy.2
  have hma : x.numerator.length*(x.numerator.length+y.denominator.length+1) ≤ b*(2*b+1) :=
    Nat.mul_le_mul hx1 (by omega)
  have hmb : y.numerator.length*(y.numerator.length+x.denominator.length+1) ≤ b*(2*b+1) :=
    Nat.mul_le_mul hy1 (by omega)
  have hmd : x.denominator.length*(x.denominator.length+y.denominator.length+1) ≤ b*(2*b+1) :=
    Nat.mul_le_mul hx2 (by omega)
  have hmax : max (mulBits x.numerator y.denominator).1.length
      (mulBits y.numerator x.denominator).1.length ≤ 3*b := by omega
  simp only [subtract]
  nlinarith

/-- Form a raw (not yet profit-scaled) option using only binary fractions. -/
def makeOption (v diff u : Fraction) : KnapsackCostState.Item × ℕ :=
  let weight := divideFresh u v
  let profit := multiplyFresh u diff
  (⟨u,weight.1,profit.1,[]⟩,weight.2+profit.2+4)

lemma makeOption_decode (v diff u : Fraction) :
    (makeOption v diff u).1.decode = ⟨u.decode,u.decode/v.decode,diff.decode*u.decode⟩ := by
  simp only [makeOption, KnapsackCostState.Item.decode, divideFresh_decode, multiplyFresh_decode]
  congr 1
  ring

lemma makeOption_valid {v diff u : Fraction} (hu : u.Valid) (hd : diff.Valid)
    (hv : 0 < v.decode) : (makeOption v diff u).1.Valid :=
  ⟨hu, divideFresh_valid hu hv, multiplyFresh_valid hu hd⟩

lemma makeOption_width {v diff u : Fraction} {a b : ℕ}
    (hu : u.Width a) (hv : v.Width b) (hd : diff.Width b) :
    (makeOption v diff u).1.Width (a+2*b) :=
  ⟨KnapsackCostState.Fraction.width_mono hu (by omega), divideFresh_width hu hv,
    multiplyFresh_width hu hd, by simp [makeOption]⟩

lemma makeOption_cost {v diff u : Fraction} {a b : ℕ}
    (hu : u.Width a) (hv : v.Width b) (hd : diff.Width b) :
    (makeOption v diff u).2 ≤ 512*(a+b+1)^2+18 := by
  have h₁ := divideFresh_cost hu hv
  have h₂ := multiplyFresh_cost hu hd
  simp only [makeOption]
  omega

def mapOptions : Fraction → Fraction → List Fraction → List KnapsackCostState.Item × ℕ
  | _, _, [] => ([],1)
  | v, diff, u::us =>
      let head := makeOption v diff u
      let tail := mapOptions v diff us
      (head.1::tail.1,head.2+tail.2+4)

lemma mapOptions_eq (v diff : Fraction) (us : List Fraction) :
    (mapOptions v diff us).1 = us.map (fun u => (makeOption v diff u).1) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [mapOptions,ih]

lemma mapOptions_cost {v diff : Fraction} {us : List Fraction} {a b : ℕ}
    (hv : v.Width b) (hd : diff.Width b) (hu : ∀ u ∈ us, u.Width a) :
    (mapOptions v diff us).2 ≤ us.length*(512*(a+b+1)^2+22)+1 := by
  induction us with
  | nil => simp [mapOptions]
  | cons u us ih =>
    have hh := makeOption_cost (hu u (by simp)) hv hd
    have ht := ih (fun u hu' => hu u (by simp [hu']))
    simp only [mapOptions,List.length_cons]
    nlinarith

def zeroItem : KnapsackCostState.Item :=
  ⟨KnapsackCostState.zero,KnapsackCostState.zero,KnapsackCostState.zero,[]⟩

lemma zeroItem_decode : zeroItem.decode = ⟨0,0,0⟩ := by
  simp [zeroItem,KnapsackCostState.Item.decode,KnapsackCostState.zero,Fraction.decode,value]
lemma zeroItem_valid : zeroItem.Valid := by
  simp [zeroItem,KnapsackCostState.Item.Valid,KnapsackCostState.zero,Fraction.Valid,value]
lemma zeroItem_width : zeroItem.Width 1 := by
  simp [zeroItem,KnapsackCostState.Item.Width,KnapsackCostState.zero,Fraction.Width]

def groupBits (horizon : ℕ) (τ ratio α v r ρ : Fraction) : List KnapsackCostState.Item × ℕ :=
  let cmp := KnapsackCostRational.compare ρ r
  if cmp.1 = .lt then
    let balanceCap := divideFresh τ α
    let cap := FPTASCostSeeds.choose true v balanceCap.1
    let options := gridBits (horizon+1) τ ratio cap.1
    let diff := subtract r ρ
    let items := mapOptions v diff.1 options.1
    (zeroItem::items.1,cmp.2+balanceCap.2+cap.2+options.2+diff.2+items.2+12)
  else ([zeroItem],cmp.2+4)

lemma positive_profit_filter (us : List ℚ) (r ρ : ℚ) (hu : ∀ u ∈ us, 0 < u) :
    us.filter (fun u => 0 < (r-ρ)*u) = if ρ < r then us else [] := by
  induction us with
  | nil => simp
  | cons u us ih =>
    have hu' := hu u (by simp)
    have ht := ih (fun u hu' => hu u (by simp [hu']))
    by_cases h : ρ < r
    · have hp : 0 < (r-ρ)*u := mul_pos (sub_pos.mpr h) hu'
      simp only [List.filter_cons,hp,decide_true,↓reduceIte,ht,if_pos h]
    · have hp : ¬ 0 < (r-ρ)*u := by
        have hh : r-ρ ≤ 0 := by linarith
        exact not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hh hu'.le)
      simp only [List.filter_cons,hp,decide_false,ht,if_neg h]
      simp

/-- Exact group-generation refinement for any sufficiently long (possibly
unreduced-bit-derived) horizon. No canonical rational normalization is needed. -/
theorem groupBits_decode (horizon : ℕ) (τ ratio α v r ρ : Fraction) (δ : ℚ)
    (ht : τ.Valid) (hratio : ratio.Valid) (ha : α.Valid) (hv : v.Valid) (hr : r.Valid) (hp : ρ.Valid)
    (htpos : 0 < τ.decode) (hapos : 0 < α.decode) (hvpos : 0 < v.decode)
    (hd : 0 < δ) (hrr : ratio.decode = 1+δ)
    (hcover : min v.decode (τ.decode/α.decode) < τ.decode*(1+δ)^(horizon+1)) :
    (groupBits horizon τ ratio α v r ρ).1.map KnapsackCostState.Item.decode =
      ⟨0,0,0⟩ :: (((Grids.geometricGrid τ.decode δ (min v.decode (τ.decode/α.decode))
        (GridBounds.gridHorizon τ.decode δ (min v.decode (τ.decode/α.decode))))).filter
          (fun u => 0 < (r.decode-ρ.decode)*u)).map
            (fun u => ⟨u,u/v.decode,(r.decode-ρ.decode)*u⟩) := by
  let us := Grids.geometricGrid τ.decode δ (min v.decode (τ.decode/α.decode))
    (GridBounds.gridHorizon τ.decode δ (min v.decode (τ.decode/α.decode)))
  have hus : ∀ u ∈ us, 0 < u := fun u hu =>
    htpos.trans_le (Grids.grid_lower_bound htpos.le hd.le hu)
  have hfilter := positive_profit_filter us r.decode ρ.decode hus
  have hcmp := KnapsackCostState.compare_fraction_lt hp hr
  by_cases hpr : ρ.decode < r.decode
  · have hclt := hcmp.mpr hpr
    have hcapv := FPTASCostSeeds.choose_valid true hv (divideFresh_valid ht hapos)
    have hcapd : (FPTASCostSeeds.choose true v (divideFresh τ α).1).1.decode =
        min v.decode (τ.decode/α.decode) := by
      rw [FPTASCostSeeds.choose_decode true hv (divideFresh_valid ht hapos), divideFresh_decode]
      rfl
    have hgrid := gridBits_refines horizon τ ratio (FPTASCostSeeds.choose true v (divideFresh τ α).1).1
      ht hratio hcapv τ.decode δ (min v.decode (τ.decode/α.decode)) rfl hrr hcapd
    rw [Grids.geometricGrid_eq_canonical htpos hd (lt_min hvpos (div_pos htpos hapos)) hcover] at hgrid
    have hdiff := subtract_decode hr hp hpr.le
    simp only [groupBits,hclt,↓reduceIte,List.map_cons,zeroItem_decode,mapOptions_eq,List.map_map]
    change _ = _
    rw [show (us.filter (fun u => 0 < (r.decode-ρ.decode)*u)) = us by simpa only [if_pos hpr] using hfilter]
    congr 1
    calc
      _ = ((gridBits (horizon+1) τ ratio (FPTASCostSeeds.choose true v (divideFresh τ α).1).1).1.map Fraction.decode).map
          (fun u => (⟨u,u/v.decode,(r.decode-ρ.decode)*u⟩ : Knapsack.Item)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro u _
        simpa only [Function.comp_apply,hdiff] using makeOption_decode v (subtract r ρ).1 u
      _ = _ := by rw [hgrid]
  · have hclt : (KnapsackCostRational.compare ρ r).1 ≠ .lt := fun h => hpr (hcmp.mp h)
    simp only [groupBits,hclt,↓reduceIte,List.map_cons,List.map_nil,zeroItem_decode]
    rw [show (us.filter (fun u => 0 < (r.decode-ρ.decode)*u)) = [] by simpa only [if_neg hpr] using hfilter]
    rfl

theorem groupBits_length (horizon : ℕ) (τ ratio α v r ρ : Fraction) :
    (groupBits horizon τ ratio α v r ρ).1.length ≤ horizon+2 := by
  have hh := gridBits_length (horizon+1) τ ratio (FPTASCostSeeds.choose true v (divideFresh τ α).1).1
  simp only [groupBits]
  split_ifs <;> simp only [List.length_cons,List.length_nil,mapOptions_eq,List.length_map] <;> omega

theorem groupBits_valid (horizon : ℕ) (τ ratio α v r ρ : Fraction)
    (ht : τ.Valid) (hratio : ratio.Valid) (hr : r.Valid) (hp : ρ.Valid)
    (hapos : 0 < α.decode) (hvpos : 0 < v.decode) :
    ∀ i ∈ (groupBits horizon τ ratio α v r ρ).1, i.Valid := by
  intro i hi
  simp only [groupBits] at hi
  split_ifs at hi
  · rcases List.mem_cons.mp hi with rfl | hi
    · exact zeroItem_valid
    · rw [mapOptions_eq] at hi
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hi
      exact makeOption_valid (gridBits_valid _ _ _ _ ht hratio u hu) (subtract_valid hr hp) hvpos
  · have he := List.mem_singleton.mp hi
    subst i
    exact zeroItem_valid

def groupWidth (h b : ℕ) : ℕ := b+2*b*(h+1)+6*b+1

theorem groupBits_width (horizon : ℕ) (τ ratio α v r ρ : Fraction) {b : ℕ}
    (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b)
    (hv : v.Width b) (hr : r.Width b) (hp : ρ.Width b) :
    ∀ i ∈ (groupBits horizon τ ratio α v r ρ).1, i.Width (groupWidth horizon b) := by
  intro i hi
  simp only [groupBits] at hi
  split_ifs at hi
  · rcases List.mem_cons.mp hi with rfl | hi
    · refine ⟨KnapsackCostState.Fraction.width_mono zeroItem_width.1 (by unfold groupWidth; omega),
        KnapsackCostState.Fraction.width_mono zeroItem_width.2.1 (by unfold groupWidth; omega),
        KnapsackCostState.Fraction.width_mono zeroItem_width.2.2.1 (by unfold groupWidth; omega), ?_⟩
      exact zeroItem_width.2.2.2.trans (by unfold groupWidth; omega)
    · rw [mapOptions_eq] at hi
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hi
      have huw := gridBits_width _ _ _ _ ht hratio u hu
      have hdiff := subtract_width hr hp
      have hv' := KnapsackCostState.Fraction.width_mono hv (show b ≤ 3*b by omega)
      have hh := makeOption_width huw hv' hdiff
      exact ⟨KnapsackCostState.Fraction.width_mono hh.1 (by unfold groupWidth; omega),
        KnapsackCostState.Fraction.width_mono hh.2.1 (by unfold groupWidth; omega),
        KnapsackCostState.Fraction.width_mono hh.2.2.1 (by unfold groupWidth; omega),
        hh.2.2.2.trans (by unfold groupWidth; omega)⟩
  · have he : i = zeroItem := List.mem_singleton.mp hi
    subst i
    refine ⟨KnapsackCostState.Fraction.width_mono zeroItem_width.1 (by unfold groupWidth; omega),
      KnapsackCostState.Fraction.width_mono zeroItem_width.2.1 (by unfold groupWidth; omega),
      KnapsackCostState.Fraction.width_mono zeroItem_width.2.2.1 (by unfold groupWidth; omega), ?_⟩
    exact zeroItem_width.2.2.2.trans (by unfold groupWidth; omega)

def groupCost (h b : ℕ) : ℕ :=
  512*(b+1)^2 + (256*(2*b+1)^2+8) + (512*(3*b+1)^2+6) +
    ((h+1)*(2048*(b+2*b*(h+1)+b+3*b+2)^2+20)+1) + 1024*(b+1)^2 +
    ((h+1)*(512*(b+2*b*(h+1)+3*b+1)^2+22)+1) + 12

theorem groupBits_cost (horizon : ℕ) (τ ratio α v r ρ : Fraction) {b : ℕ}
    (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b)
    (hv : v.Width b) (hr : r.Width b) (hp : ρ.Width b) :
    (groupBits horizon τ ratio α v r ρ).2 ≤ groupCost horizon b := by
  have hcmp := compare_cost hp hr
  have hbal := divideFresh_cost ht ha
  have hbalw := divideFresh_width ht ha
  have hv' := KnapsackCostState.Fraction.width_mono hv (show b ≤ 3*b by omega)
  have hbalw' : (divideFresh τ α).1.Width (3*b) := by convert hbalw using 1 <;> omega
  have hcap := FPTASCostSeeds.choose_cost true hv' hbalw'
  have hcapw := FPTASCostSeeds.choose_width true hv' hbalw'
  have hgrid := gridBits_cost (horizon+1) τ ratio (FPTASCostSeeds.choose true v (divideFresh τ α).1).1 ht hratio hcapw
  have hgridw := gridBits_width (horizon+1) τ ratio (FPTASCostSeeds.choose true v (divideFresh τ α).1).1 ht hratio
  have hgridlen := gridBits_length (horizon+1) τ ratio (FPTASCostSeeds.choose true v (divideFresh τ α).1).1
  have hdiff := subtract_cost hr hp
  have hdiffw := subtract_width hr hp
  have hmap := mapOptions_cost hv' hdiffw hgridw
  have hmul := Nat.mul_le_mul_right (512*(b+2*b*(horizon+1)+3*b+1)^2+22) hgridlen
  simp only [groupBits,groupCost]
  split_ifs <;> nlinarith

end BalancedAssortments.FPTASCostOptions
