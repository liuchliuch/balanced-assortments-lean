import Mathlib

namespace BalancedAssortments.FixedSupportAlgorithm

section OrderedField
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Endpoints plus every pairwise midpoint. Redundant samples avoid an
algorithmic adjacency oracle and retain a polynomial-size arrangement. -/
def regimeSamples (C : Finset 𝕜) : Finset 𝕜 :=
  C ∪ (C.product C).image (fun p => (p.1 + p.2) / 2)

def SameRegion (C : Finset 𝕜) (x s : 𝕜) : Prop :=
  ∀ c ∈ C, (c < x ↔ c < s) ∧ (x < c ↔ s < c)

theorem regimeSamples_card (C : Finset 𝕜) :
    (regimeSamples C).card ≤ C.card + C.card ^ 2 := by
  calc
    (regimeSamples C).card ≤ C.card + ((C.product C).image (fun p => (p.1 + p.2) / 2)).card :=
      Finset.card_union_le _ _
    _ ≤ C.card + (C.product C).card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = C.card + C.card ^ 2 := by simp [pow_two]

theorem regimeSamples_bounds {C : Finset 𝕜} {lo hi : 𝕜}
    (hC : ∀ c ∈ C, lo ≤ c ∧ c ≤ hi) {s : 𝕜} (hs : s ∈ regimeSamples C) :
    lo ≤ s ∧ s ≤ hi := by
  rcases Finset.mem_union.mp hs with hs | hs
  · exact hC s hs
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hs
    have ha := hC a (Finset.mem_product.mp hab).1
    have hb := hC b (Finset.mem_product.mp hab).2
    constructor <;> linarith

/-- Every point between the extreme critical cuts has a sampled point with
exactly the same weak-order regime, including all endpoint equalities. -/
theorem exists_regime_sample {C : Finset 𝕜} {lo hi x : 𝕜}
    (hlo : lo ∈ C) (hhi : hi ∈ C) (hx : lo ≤ x ∧ x ≤ hi) :
    ∃ s ∈ regimeSamples C, SameRegion C x s := by
  by_cases hxc : x ∈ C
  · exact ⟨x, Finset.mem_union_left _ hxc, fun _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  let A := C.filter (fun c => c ≤ x)
  let B := C.filter (fun c => x ≤ c)
  have hA : A.Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨hlo, hx.1⟩⟩
  have hB : B.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨hhi, hx.2⟩⟩
  let a := A.max' hA
  let b := B.min' hB
  have ha : a ∈ C ∧ a ≤ x := Finset.mem_filter.mp (A.max'_mem hA)
  have hb : b ∈ C ∧ x ≤ b := Finset.mem_filter.mp (B.min'_mem hB)
  have hax : a < x := lt_of_le_of_ne ha.2 (fun he => hxc (he ▸ ha.1))
  have hxb : x < b := lt_of_le_of_ne hb.2 (fun he => hxc (he.symm ▸ hb.1))
  let s := (a + b) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsb : s < b := by dsimp [s]; linarith
  refine ⟨s, Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_product.mpr ⟨ha.1, hb.1⟩, rfl⟩), ?_⟩
  intro c hc
  by_cases hcx : c ≤ x
  · have hca : c ≤ a := A.le_max' c (Finset.mem_filter.mpr ⟨hc, hcx⟩)
    have hcx' : c < x := lt_of_le_of_ne hcx (fun he => hxc (he ▸ hc))
    have hcs : c < s := hca.trans_lt has
    exact ⟨iff_of_true hcx' hcs, iff_of_false (not_lt_of_ge hcx'.le) (not_lt_of_ge hcs.le)⟩
  · have hxc' : x < c := lt_of_not_ge hcx
    have hbc : b ≤ c := B.min'_le c (Finset.mem_filter.mpr ⟨hc, hxc'.le⟩)
    have hsc : s < c := hsb.trans_le hbc
    exact ⟨iff_of_false (not_lt_of_ge hxc'.le) (not_lt_of_ge hsc.le), iff_of_true hxc' hsc⟩

abbrev Affine := 𝕜 × 𝕜

def affineValue (f : Affine (𝕜 := 𝕜)) (x : 𝕜) : 𝕜 := f.1 * x + f.2

def affineRoot (f : Affine (𝕜 := 𝕜)) : 𝕜 := -f.2 / f.1

def affineCritical (lo hi : 𝕜) (F : Finset (Affine (𝕜 := 𝕜))) : Finset 𝕜 :=
  insert lo (insert hi (((F.filter (fun f => f.1 ≠ 0)).image affineRoot).filter
    (fun c => lo ≤ c ∧ c ≤ hi)))

theorem affineCritical_bounds {lo hi : 𝕜} (h : lo ≤ hi)
    (F : Finset (Affine (𝕜 := 𝕜))) :
    ∀ c ∈ affineCritical lo hi F, lo ≤ c ∧ c ≤ hi := by
  intro c hc
  simp only [affineCritical, Finset.mem_insert, Finset.mem_filter] at hc
  rcases hc with rfl | rfl | ⟨_, hc⟩
  · exact ⟨le_rfl, h⟩
  · exact ⟨h, le_rfl⟩
  · exact hc

private theorem cut_same_region {C : Finset 𝕜} {lo hi x s c : 𝕜}
    (hx : lo ≤ x ∧ x ≤ hi) (hs : lo ≤ s ∧ s ≤ hi)
    (hreg : SameRegion C x s) (hc : lo ≤ c → c ≤ hi → c ∈ C) :
    (c < x ↔ c < s) ∧ (x < c ↔ s < c) := by
  by_cases hl : lo ≤ c
  · by_cases hh : c ≤ hi
    · exact hreg c (hc hl hh)
    · have hhi : hi < c := lt_of_not_ge hh
      have hxc := hx.2.trans_lt hhi
      have hsc := hs.2.trans_lt hhi
      exact ⟨iff_of_false (not_lt_of_ge hxc.le) (not_lt_of_ge hsc.le), iff_of_true hxc hsc⟩
  · have hcl : c < lo := lt_of_not_ge hl
    have hcx := hcl.trans_le hx.1
    have hcs := hcl.trans_le hs.1
    exact ⟨iff_of_true hcx hcs, iff_of_false (not_lt_of_ge hcx.le) (not_lt_of_ge hcs.le)⟩

/-- A sampled regime preserves every affine sign and every endpoint equality.
Constant affine functions and roots outside the domain are handled explicitly. -/
theorem affine_signs_same {F : Finset (Affine (𝕜 := 𝕜))} {lo hi x s : 𝕜}
    (hx : lo ≤ x ∧ x ≤ hi) (hs : lo ≤ s ∧ s ≤ hi)
    (hreg : SameRegion (affineCritical lo hi F) x s) {f : Affine (𝕜 := 𝕜)} (hf : f ∈ F) :
    (affineValue f x ≤ 0 ↔ affineValue f s ≤ 0) ∧
      (0 ≤ affineValue f x ↔ 0 ≤ affineValue f s) := by
  by_cases hz : f.1 = 0
  · simp [affineValue, hz]
  · have hc := cut_same_region hx hs hreg (c := affineRoot f) (fun hl hh => by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨f, Finset.mem_filter.mpr ⟨hf, hz⟩, rfl⟩, hl, hh⟩)
    have hle1 : x ≤ affineRoot f ↔ s ≤ affineRoot f := by
      simpa only [not_lt] using not_congr hc.1
    have hle2 : affineRoot f ≤ x ↔ affineRoot f ≤ s := by
      simpa only [not_lt] using not_congr hc.2
    have he (y : 𝕜) : affineValue f y = f.1 * (y - affineRoot f) := by
      dsimp [affineValue, affineRoot]
      field_simp
      <;> ring
    constructor
    · simp only [he, mul_nonpos_iff, sub_nonneg, sub_nonpos, hle1, hle2]
    · simp only [he, mul_nonneg_iff, sub_nonneg, sub_nonpos, hle1, hle2]

/-- Finite arrangement coverage, valid over any ordered field. -/
theorem affine_regime_coverage {lo hi x : 𝕜} (hdom : lo ≤ hi)
    (F : Finset (Affine (𝕜 := 𝕜))) (hx : lo ≤ x ∧ x ≤ hi) :
    ∃ s ∈ regimeSamples (affineCritical lo hi F), lo ≤ s ∧ s ≤ hi ∧
      ∀ f ∈ F, (affineValue f x ≤ 0 ↔ affineValue f s ≤ 0) ∧
        (0 ≤ affineValue f x ↔ 0 ≤ affineValue f s) := by
  obtain ⟨s, hs, hreg⟩ := exists_regime_sample
    (C := affineCritical lo hi F) (lo := lo) (hi := hi) (by simp [affineCritical])
    (by simp [affineCritical]) hx
  have hsb := regimeSamples_bounds (affineCritical_bounds hdom F) hs
  exact ⟨s, hs, hsb.1, hsb.2, fun f hf => affine_signs_same hx hsb hreg hf⟩

/-- The sign argument also applies to any finite cut superset containing all
relevant roots; this supports exact rational samples for a real target. -/
theorem affine_signs_same_of_roots {C : Finset 𝕜} {lo hi x s : 𝕜}
    (hx : lo ≤ x ∧ x ≤ hi) (hs : lo ≤ s ∧ s ≤ hi) (hreg : SameRegion C x s)
    (f : Affine (𝕜 := 𝕜))
    (hroot : f.1 ≠ 0 → lo ≤ affineRoot f → affineRoot f ≤ hi → affineRoot f ∈ C) :
    (affineValue f x ≤ 0 ↔ affineValue f s ≤ 0) ∧
      (0 ≤ affineValue f x ↔ 0 ≤ affineValue f s) := by
  by_cases hz : f.1 = 0
  · simp [affineValue, hz]
  · have hc := cut_same_region hx hs hreg (hroot hz)
    have hle1 : x ≤ affineRoot f ↔ s ≤ affineRoot f := by
      simpa only [not_lt] using not_congr hc.1
    have hle2 : affineRoot f ≤ x ↔ affineRoot f ≤ s := by
      simpa only [not_lt] using not_congr hc.2
    have he (y : 𝕜) : affineValue f y = f.1 * (y - affineRoot f) := by
      dsimp [affineValue, affineRoot]
      field_simp
      <;> ring
    constructor
    · simp only [he, mul_nonpos_iff, sub_nonneg, sub_nonpos, hle1, hle2]
    · simp only [he, mul_nonneg_iff, sub_nonneg, sub_nonpos, hle1, hle2]

end OrderedField
end BalancedAssortments.FixedSupportAlgorithm
