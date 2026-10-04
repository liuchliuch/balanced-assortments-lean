import BalancedAssortments.FPTASCostGroups
import BalancedAssortments.FPTASCostGridFuel

/-! Actual charged option generation with automatically constructed structural
fuel. Both the cap seed and every token-generation operation are included. -/
namespace BalancedAssortments.FPTASCostOptions
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid FPTASCostSeeds

/-- The group evaluator consumes list tokens directly, with no decoded numeric
loop count. All other operations match the previously refined group kernel. -/
def groupTokens (fuel : List Unit) (τ ratio α v r ρ : Fraction) : List KnapsackCostState.Item × ℕ :=
  let cmp := compare ρ r
  if cmp.1 = .lt then
    let balanceCap := divideFresh τ α
    let cap := FPTASCostSeeds.choose true v balanceCap.1
    let options := gridTokens fuel τ ratio cap.1
    let diff := subtract r ρ
    let items := mapOptions v diff.1 options.1
    (zeroItem::items.1,cmp.2+balanceCap.2+cap.2+options.2+diff.2+items.2+12)
  else ([zeroItem],cmp.2+4)

/-- Equality covers the entire returned pair, including its charged cost. -/
theorem groupTokens_eq (fuel : List Unit) (H : ℕ) (hlen : fuel.length = H+1)
    (τ ratio α v r ρ : Fraction) : groupTokens fuel τ ratio α v r ρ = groupBits H τ ratio α v r ρ := by
  simp only [groupTokens,groupBits,gridTokens_eq,hlen]

def autoCap (τ α v : Fraction) : Fraction := (FPTASCostSeeds.choose true v (divideFresh τ α).1).1

def autoHorizon (τ delta α v : Fraction) : ℕ := rawHorizon τ delta (autoCap τ α v)

/-- This intentionally reuses groupTokens unchanged; repeated cap computation
inside the kernel is paid for rather than hidden or identified for free. -/
def groupAuto (τ delta ratio α v r ρ : Fraction) : List KnapsackCostState.Item × ℕ :=
  let balanceCap := divideFresh τ α
  let cap := FPTASCostSeeds.choose true v balanceCap.1
  let fuel := rawGridFuel τ delta cap.1
  let generated := groupTokens fuel.1 τ ratio α v r ρ
  (generated.1,balanceCap.2+cap.2+fuel.2+generated.2+8)

theorem groupAuto_output (τ delta ratio α v r ρ : Fraction) :
    (groupAuto τ delta ratio α v r ρ).1 =
      (groupBits (autoHorizon τ delta α v) τ ratio α v r ρ).1 := by
  unfold groupAuto
  dsimp only
  have he := groupTokens_eq (rawGridFuel τ delta (autoCap τ α v)).1
    (autoHorizon τ delta α v) (rawGridFuel_length τ delta (autoCap τ α v)) τ ratio α v r ρ
  simp only [autoCap] at he
  rw [he]

lemma autoCap_valid {τ α v : Fraction} (ht : τ.Valid) (hv : v.Valid) (ha : 0 < α.decode) :
    (autoCap τ α v).Valid := choose_valid true hv (divideFresh_valid ht ha)

lemma autoCap_decode {τ α v : Fraction} (ht : τ.Valid) (hv : v.Valid) (ha : 0 < α.decode) :
    (autoCap τ α v).decode = min v.decode (τ.decode/α.decode) := by
  unfold autoCap
  rw [choose_decode true hv (divideFresh_valid ht ha),divideFresh_decode]
  rfl

lemma autoCap_width {τ α v : Fraction} {b : ℕ} (ht : τ.Width b) (ha : α.Width b) (hv : v.Width b) :
    (autoCap τ α v).Width (3*b) := by
  have hbal := divideFresh_width ht ha
  apply choose_width true
  · exact KnapsackCostState.Fraction.width_mono hv (by omega)
  · convert hbal using 1 <;> omega

lemma autoHorizon_bound {τ delta α v : Fraction} {b : ℕ}
    (ht : τ.Width b) (ha : α.Width b) (hv : v.Width b) :
    autoHorizon τ delta α v ≤ 4*b*value (reciprocalCeilingBits delta).1 := by
  have hc := autoCap_width ht ha hv
  unfold autoHorizon rawHorizon
  have hL : τ.denominator.length+(autoCap τ α v).numerator.length ≤ 4*b := by
    have htd := ht.2
    have hcn := hc.1
    omega
  nlinarith

lemma groupCost_mono {h H b : ℕ} (hH : h ≤ H) : groupCost h b ≤ groupCost H b := by
  unfold groupCost
  gcongr

lemma groupWidth_mono {h H b : ℕ} (hH : h ≤ H) : groupWidth h b ≤ groupWidth H b := by
  unfold groupWidth
  gcongr

lemma reciprocalCeilingBits_width {delta : Fraction} {b : ℕ} (hb : 1 ≤ b) (hd : delta.Width b) :
    (reciprocalCeilingBits delta).1.length ≤ 3*b+1 := by
  have hone : FPTASCostSeeds.one.Width b := ⟨one_width.1.trans hb,one_width.2.trans hb⟩
  have h := floorRatio_width hone hd
  simp only [reciprocalCeilingBits,addCarry_length,List.length_cons,List.length_nil]
  omega

def autoGroupCost (b Q : ℕ) : ℕ :=
  (256*(2*b+1)^2+8)+(512*(3*b+1)^2+6)+
    (4096*(b+1)^2+100*b+50+Q*(4*b+6))+groupCost (4*b*Q) b+8

/-- All raw arithmetic and potentially inverse-accuracy-sized fuel materialization
are included in this cost. Q is the decoded safe reciprocal ceiling only in the bound. -/
theorem groupAuto_cost (τ delta ratio α v r ρ : Fraction) {b : ℕ}
    (hb : 1 ≤ b) (ht : τ.Width b) (hd : delta.Width b) (hratio : ratio.Width b)
    (ha : α.Width b) (hv : v.Width b) (hr : r.Width b) (hp : ρ.Width b) :
    (groupAuto τ delta ratio α v r ρ).2 ≤ autoGroupCost b (value (reciprocalCeilingBits delta).1) := by
  have hcW := autoCap_width ht ha hv
  have hbal := divideFresh_cost ht ha
  have hbw := divideFresh_width ht ha
  have hcap := choose_cost true (KnapsackCostState.Fraction.width_mono hv (show b ≤ 3*b by omega))
    (show (divideFresh τ α).1.Width (3*b) by convert hbw using 1 <;> omega)
  have hFuel := rawGridFuel_cost τ delta (autoCap τ α v)
  have hRec := reciprocalCeilingBits_cost delta hb hd
  have hRecW := reciprocalCeilingBits_width hb hd
  have hL : τ.denominator.length+(autoCap τ α v).numerator.length ≤ 4*b := by
    have htd := ht.2
    have hcn := hcW.1
    omega
  have hLm := Nat.mul_le_mul_left (value (reciprocalCeilingBits delta).1) (Nat.add_le_add_right hL 6)
  have hgen := groupBits_cost (autoHorizon τ delta α v) τ ratio α v r ρ ht hratio ha hv hr hp
  have hg := groupCost_mono (b := b) (autoHorizon_bound (delta := delta) ht ha hv)
  unfold groupAuto
  dsimp only
  have he := groupTokens_eq (rawGridFuel τ delta (autoCap τ α v)).1
    (autoHorizon τ delta α v) (rawGridFuel_length τ delta (autoCap τ α v)) τ ratio α v r ρ
  simp only [autoCap] at he
  rw [he]
  unfold autoGroupCost
  dsimp only [autoCap] at hFuel hL hLm ⊢
  nlinarith

theorem groupAuto_width (τ delta ratio α v r ρ : Fraction) {b : ℕ}
    (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b)
    (hv : v.Width b) (hr : r.Width b) (hp : ρ.Width b) :
    (groupAuto τ delta ratio α v r ρ).1.length ≤ 4*b*value (reciprocalCeilingBits delta).1+2 ∧
    ∀ i ∈ (groupAuto τ delta ratio α v r ρ).1,
      i.Width (groupWidth (4*b*value (reciprocalCeilingBits delta).1) b) := by
  rw [groupAuto_output]
  have hh := autoHorizon_bound (delta := delta) ht ha hv
  refine ⟨(groupBits_length _ _ _ _ _ _ _).trans (by omega), ?_⟩
  intro i hi
  have hw := groupBits_width _ _ _ _ _ _ _ ht hratio ha hv hr hp i hi
  have hm := groupWidth_mono (b := b) hh
  exact ⟨KnapsackCostState.Fraction.width_mono hw.1 hm,
    KnapsackCostState.Fraction.width_mono hw.2.1 hm,
    KnapsackCostState.Fraction.width_mono hw.2.2.1 hm,hw.2.2.2.trans hm⟩

/-- Exact automatic-horizon refinement; no coverage premise is left to the caller. -/
theorem groupAuto_decode (τ delta ratio α v r ρ : Fraction)
    (ht : τ.Valid) (hd : delta.Valid) (hratio : ratio.Valid) (ha : α.Valid)
    (hv : v.Valid) (hr : r.Valid) (hp : ρ.Valid)
    (htpos : 0 < τ.decode) (hdpos : 0 < delta.decode) (hapos : 0 < α.decode)
    (hvpos : 0 < v.decode) (hrat : ratio.decode = 1+delta.decode) :
    (groupAuto τ delta ratio α v r ρ).1.map KnapsackCostState.Item.decode =
      ⟨0,0,0⟩ :: ((Grids.geometricGrid τ.decode delta.decode (min v.decode (τ.decode/α.decode))
        (GridBounds.gridHorizon τ.decode delta.decode (min v.decode (τ.decode/α.decode)))).filter
          (fun u => 0 < (r.decode-ρ.decode)*u)).map
            (fun u => ⟨u,u/v.decode,(r.decode-ρ.decode)*u⟩) := by
  rw [groupAuto_output]
  apply groupBits_decode _ _ _ _ _ _ _ _ ht hratio ha hv hr hp htpos hapos hvpos hdpos hrat
  have hcap := autoCap_valid ht hv hapos
  have hcapd := autoCap_decode ht hv hapos
  have hcappos : 0 < (autoCap τ α v).decode := by rw [hcapd]; exact lt_min hvpos (div_pos htpos hapos)
  have hcover := GridBounds.gridHorizon_covers htpos hdpos hcappos
  have hhor := rawHorizon_ge_canonical τ delta (autoCap τ α v) ht hd hcap hdpos
  have hpow : (1+delta.decode)^GridBounds.gridHorizon τ.decode delta.decode (autoCap τ α v).decode ≤
      (1+delta.decode)^(autoHorizon τ delta α v+1) :=
    pow_le_pow_right₀ (by linarith) (by exact Nat.le_succ_of_le hhor)
  rw [hcapd] at hcover hpow
  exact hcover.trans_le (mul_le_mul_of_nonneg_left hpow htpos.le)

theorem groupAuto_valid (τ delta ratio α v r ρ : Fraction)
    (ht : τ.Valid) (hratio : ratio.Valid) (hr : r.Valid) (hp : ρ.Valid)
    (hapos : 0 < α.decode) (hvpos : 0 < v.decode) :
    ∀ i ∈ (groupAuto τ delta ratio α v r ρ).1, i.Valid := by
  rw [groupAuto_output]
  exact groupBits_valid _ _ _ _ _ _ _ ht hratio hr hp hapos hvpos

def groupsAuto (delta τ ratio α ρ : Fraction) : List (Fraction × Fraction) →
    List (List KnapsackCostState.Item) × ℕ
  | [] => ([],1)
  | (r,v)::products =>
      let g := groupAuto τ delta ratio α v r ρ
      let tail := groupsAuto delta τ ratio α ρ products
      (g.1::tail.1,g.2+tail.2+4)

theorem groupsAuto_eq (delta τ ratio α ρ : Fraction) (products : List (Fraction × Fraction)) :
    (groupsAuto delta τ ratio α ρ products).1 = products.map
      (fun rv => (groupAuto τ delta ratio α rv.2 rv.1 ρ).1) := by
  induction products with
  | nil => rfl
  | cons rv products ih => cases rv; simp [groupsAuto,ih]

@[simp] theorem groupsAuto_length (delta τ ratio α ρ : Fraction) (products : List (Fraction × Fraction)) :
    (groupsAuto delta τ ratio α ρ products).1.length = products.length := by
  rw [groupsAuto_eq,List.length_map]

theorem autoGroupCost_mono {b Q R : ℕ} (h : Q ≤ R) : autoGroupCost b Q ≤ autoGroupCost b R := by
  unfold autoGroupCost groupCost
  gcongr

theorem groupsAuto_cost (delta τ ratio α ρ : Fraction) (products : List (Fraction × Fraction)) {b : ℕ}
    (hb : 1 ≤ b) (hd : delta.Width b) (ht : τ.Width b) (hratio : ratio.Width b)
    (ha : α.Width b) (hp : ρ.Width b)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    (groupsAuto delta τ ratio α ρ products).2 ≤
      products.length*(autoGroupCost b (value (reciprocalCeilingBits delta).1)+4)+1 := by
  induction products with
  | nil => simp [groupsAuto]
  | cons rv products ih =>
    obtain ⟨r,v⟩ := rv
    have hw := hprod (r,v) (by simp)
    have hg := groupAuto_cost τ delta ratio α v r ρ hb ht hd hratio ha hw.2 hw.1 hp
    have hh := ih (fun rv hrv => hprod rv (by simp [hrv]))
    simp only [groupsAuto,List.length_cons]
    nlinarith

/-- Uniform polynomial cost in the conventional reciprocal-accuracy parameter. -/
theorem groupsAuto_cost_ceil (delta τ ratio α ρ : Fraction) (products : List (Fraction × Fraction)) {b : ℕ}
    (hb : 1 ≤ b) (hd : delta.Width b) (ht : τ.Width b) (hratio : ratio.Width b)
    (ha : α.Width b) (hp : ρ.Width b) (hdv : delta.Valid) (hdpos : 0 < delta.decode)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    (groupsAuto delta τ ratio α ρ products).2 ≤
      products.length*(autoGroupCost b (GridBounds.blockLength delta.decode+1)+4)+1 := by
  have h := groupsAuto_cost delta τ ratio α ρ products hb hd ht hratio ha hp hprod
  have hm := autoGroupCost_mono (b := b) (reciprocalCeilingBits_le_succ delta hdv hdpos)
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left products.length (Nat.add_le_add_right hm 4)) 1)

theorem groupsAuto_bounds (delta τ ratio α ρ : Fraction) (products : List (Fraction × Fraction)) {b : ℕ}
    (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b) (hp : ρ.Width b)
    (hdv : delta.Valid) (hdpos : 0 < delta.decode)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    ∀ g ∈ (groupsAuto delta τ ratio α ρ products).1,
      g.length ≤ 4*b*(GridBounds.blockLength delta.decode+1)+2 ∧
      ∀ i ∈ g, i.Width (groupWidth (4*b*(GridBounds.blockLength delta.decode+1)) b) := by
  intro g hg
  rw [groupsAuto_eq] at hg
  obtain ⟨rv,hrv,rfl⟩ := List.mem_map.mp hg
  have hh := groupAuto_width τ delta ratio α rv.2 rv.1 ρ ht hratio ha (hprod rv hrv).2 (hprod rv hrv).1 hp
  have hq := reciprocalCeilingBits_le_succ delta hdv hdpos
  have hmul := Nat.mul_le_mul_left (4*b) hq
  refine ⟨hh.1.trans (by omega),?_⟩
  intro i hi
  have hw := hh.2 i hi
  have hm := groupWidth_mono (b := b) hmul
  exact ⟨KnapsackCostState.Fraction.width_mono hw.1 hm,
    KnapsackCostState.Fraction.width_mono hw.2.1 hm,
    KnapsackCostState.Fraction.width_mono hw.2.2.1 hm,hw.2.2.2.trans hm⟩

theorem groupsAuto_valid (delta τ ratio α ρ : Fraction) (products : List (Fraction × Fraction))
    (ht : τ.Valid) (hratio : ratio.Valid) (hp : ρ.Valid) (hapos : 0 < α.decode)
    (hprod : ∀ rv ∈ products, rv.1.Valid ∧ 0 < rv.2.decode) :
    ∀ g ∈ (groupsAuto delta τ ratio α ρ products).1, ∀ i ∈ g, i.Valid := by
  intro g hg
  rw [groupsAuto_eq] at hg
  obtain ⟨rv,hrv,rfl⟩ := List.mem_map.mp hg
  exact groupAuto_valid _ _ _ _ _ _ _ ht hratio (hprod rv hrv).1 hp hapos (hprod rv hrv).2

/-- Exact refinement of all actual auto-generated groups, with every individual
cap and grid horizon computed inside the executable program. -/
theorem groupsAuto_decode {n : ℕ} (d : FPTAS.Input n) (delta τ ratio α ρ : Fraction)
    (rv : Fin (n+1) → Fraction × Fraction)
    (ht : τ.Valid) (hd : delta.Valid) (hratio : ratio.Valid) (ha : α.Valid) (hp : ρ.Valid)
    (hprod : ∀ i, (rv i).1.Valid ∧ (rv i).2.Valid)
    (hdecode : ∀ i, (rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (halpha : α.decode = d.α) (hrat : ratio.decode = 1+delta.decode)
    (htpos : 0 < τ.decode) (hapos : 0 < d.α) (hvpos : ∀ i, 0 < d.v i) (hdpos : 0 < delta.decode) :
    ((groupsAuto delta τ ratio α ρ ((List.finRange (n+1)).map rv)).1.map
      (List.map KnapsackCostState.Item.decode)) = FPTAS.groups d delta.decode τ.decode ρ.decode := by
  rw [groupsAuto_eq,List.map_map,List.map_map]
  unfold FPTAS.groups
  apply List.map_congr_left
  intro i _
  have hh := groupAuto_decode τ delta ratio α (rv i).2 (rv i).1 ρ ht hd hratio ha
    (hprod i).2 (hprod i).1 hp htpos hdpos (by rwa [halpha])
    (by simpa only [(hdecode i).2] using hvpos i) hrat
  simpa only [Function.comp_apply,FPTAS.group,halpha,(hdecode i).1,(hdecode i).2] using hh

end BalancedAssortments.FPTASCostOptions
