import BalancedAssortments.FPTASCostProgram
import BalancedAssortments.FPTASCostGridUniform

namespace BalancedAssortments.FPTASCostProgram
open KnapsackCostRational FPTASCostSeeds FPTASCostGrid FPTASCostLoops
open FPTASCostCandidate FPTASCostSingletons FPTASCostCutoff

lemma autoCandidateCost_bound_mono {B C N b Q : ℕ} (h : B ≤ C) :
    autoCandidateCost B N b Q ≤ autoCandidateCost C N b Q := by
  dsimp only [autoCandidateCost,candidateCoreCost,FPTASCostKernel.coreCost,
    FPTASCost.solverBudget,KnapsackCostState.rowCost]
  gcongr

def updateBudget (N b : ℕ) : ℕ :=
  2*FPTASCostOutput.revenueBudget N b+512*(FPTASCostOutput.revenueWidth N b+1)^2+10

/-- This expression uses only addition, multiplication and fixed powers of the
raw bit-width bound, product count and reciprocal-accuracy ceiling. -/
def salesBudget (b N Q : ℕ) : ℕ :=
  let B := b+N+9
  let S := 7*B+4
  let k := gridQuota S Q
  let G := gridWidth S Q
  let C := autoCandidateCost (N^2*Q) N G Q
  let W := G+FPTASCostKernel.kernelWidth N (FPTASCostOptions.groupWidth (4*G*(Q+1)) G)+1
  (256*(b+5)^2+8+64*(N+1)^2+3+seedCost N B+4) +
    64*(N+1)^2+1 + (16384*(B+1)^2+2*(N^2*Q)+4*(5*B+2)+5) +
    2*gridBudget S Q + (k*(k*(C+5)+5)+1) +
    (8*N^2+8*N+1)+(4*N+1)+((N+k^2)*updateBudget N W+1)+3*N+k^2+20

def salesOutputWidth (b N Q : ℕ) : ℕ :=
  let G := gridWidth (7*(b+N+9)+4) Q
  G+FPTASCostKernel.kernelWidth N (FPTASCostOptions.groupWidth (4*G*(Q+1)) G)+1

/-- Complete bit/list-operation cost of the raw binary sales program, including
input counting, ε/10, seeds, fuel conversion, grids, every candidate and incumbent.
The reciprocal parameter is computed from the decoded accuracy fraction. -/
theorem runSalesBits_analysis (alpha epsilon capacity : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (he : epsilon.Width b) (hk : capacity.Width b)
    (hprod : ∀ p ∈ products,p.1.Width b ∧ p.2.Width b)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hep : 0 < epsilon.decode)
    (hprodv : ∀ p ∈ products,p.1.Valid ∧ p.2.Valid) (hne : products ≠ []) :
    (runSalesBits alpha epsilon capacity products).2 ≤
      salesBudget b products.length ⌈10/epsilon.decode⌉₊ ∧
    (runSalesBits alpha epsilon capacity products).1.length ≤ products.length ∧
    ∀ x ∈ (runSalesBits alpha epsilon capacity products).1,
      x.Width (salesOutputWidth b products.length ⌈10/epsilon.decode⌉₊) := by
  let N := products.length
  let prep := prepareSeeds alpha epsilon products
  let δ := prep.1.1
  let seeds := prep.1.2
  let counted := countBits products
  let count := countAsFraction counted.1
  let fuel := cutoffFuel counted.1 δ
  let scales := rawGrid seeds.scaleBase δ seeds.ratio seeds.scaleCap
  let revenues := rawGrid seeds.revenueBase δ seeds.ratio seeds.revenueCap
  let cand := cross (fun τ ρ => autoCandidate δ count capacity τ seeds.ratio alpha ρ fuel.1 products) scales.1 revenues.1
  let values := products.map Prod.snd
  let prices := products.map Prod.fst
  let singleton := singletons values
  let empty := zeroes values
  let vectors := cand.1.map KnapsackCostState.State.choices
  let B := b+N+9
  let S := 7*B+4
  let Q := GridBounds.blockLength δ.decode
  let k := gridQuota S Q
  let G := gridWidth S Q
  let C := autoCandidateCost (N^2*Q) N G Q
  let W := G+FPTASCostKernel.kernelWidth N (FPTASCostOptions.groupWidth (4*G*(Q+1)) G)+1
  have hdelta : δ.decode = epsilon.decode/10 := accuracyFraction_decode epsilon
  have hQ : Q = ⌈10/epsilon.decode⌉₊ := by
    dsimp [Q]
    rw [hdelta,FPTASCost.precision_parameter]
  have hδv : δ.Valid := (prepareSeeds_valid alpha epsilon products hav hev hprodv hne).1
  have hδp : 0 < δ.decode := by rw [hdelta]; positivity
  have hsv : seeds.Valid := (prepareSeeds_valid alpha epsilon products hav hev hprodv hne).2
  obtain ⟨hδw,hsw⟩ := prepareSeeds_width alpha epsilon products hb ha he hprod
  have hSB : B ≤ S := by dsimp [S]; omega
  have hGb : b ≤ G := by dsimp [G,gridWidth,S,B,N]; omega
  have hGS : S ≤ G := by dsimp [G,gridWidth]; omega
  have hδS : δ.Width S := KnapsackCostState.Fraction.width_mono hδw hSB
  have hsBounds := rawGrid_uniform_bounds seeds.scaleBase δ seeds.ratio seeds.scaleCap
    hsw.1 hsw.2.2.2.2 hsw.2.1 hδv hδp hsv.1 hsv.2.2.2.2
  have hrBounds := rawGrid_uniform_bounds seeds.revenueBase δ seeds.ratio seeds.revenueCap
    hsw.2.2.1 hsw.2.2.2.2 hsw.2.2.2.1 hδv hδp hsv.2.2.1 hsv.2.2.2.2
  have hsCost := rawGrid_uniform_cost seeds.scaleBase δ seeds.ratio seeds.scaleCap
    (show 1 ≤ S by dsimp [S]; omega) hsw.1 hδS hsw.2.2.2.2 hsw.2.1 hδv hδp
  have hrCost := rawGrid_uniform_cost seeds.revenueBase δ seeds.ratio seeds.revenueCap
    (show 1 ≤ S by dsimp [S]; omega) hsw.2.2.1 hδS hsw.2.2.2.2 hsw.2.2.2.1 hδv hδp
  have hcountBits : counted.1.length ≤ B := (countBits_width products).trans (by dsimp [B,N]; omega)
  have hcount : count.Width G := by
    refine ⟨hcountBits.trans (hSB.trans hGS), ?_⟩
    change 1 ≤ G
    exact hb.trans hGb
  have hδG := KnapsackCostState.Fraction.width_mono hδS hGS
  have halphaG := KnapsackCostState.Fraction.width_mono ha hGb
  have hcapG := KnapsackCostState.Fraction.width_mono hk hGb
  have hratioG := KnapsackCostState.Fraction.width_mono hsw.2.2.2.2 hGS
  have hprodG : ∀ rv ∈ products,rv.1.Width G ∧ rv.2.Width G := by
    intro rv hrv
    exact ⟨KnapsackCostState.Fraction.width_mono (hprod rv hrv).1 hGb,
      KnapsackCostState.Fraction.width_mono (hprod rv hrv).2 hGb⟩
  have hfLength : fuel.1.length ≤ N^2*Q := by
    have hh := cutoffFuel_length counted.1 hδp
    rw [countBits_value] at hh
    rw [hh]
    exact FPTASCost.state_cutoff_bound N δ.decode
  have hfCost := cutoffFuel_cost hcountBits (show 1 ≤ B by dsimp [B]; omega) hδw hδp
  have hfCost' : fuel.2 ≤ 16384*(B+1)^2+2*(N^2*Q)+4*(5*B+2)+5 := by
    rw [countBits_value] at hfCost
    change fuel.2 ≤ 16384*(B+1)^2+2*(N*⌈(N:ℚ)/δ.decode⌉₊)+4*(5*B+2)+5 at hfCost
    have hh : N*⌈(N:ℚ)/δ.decode⌉₊ ≤ N^2*Q := FPTASCost.state_cutoff_bound N δ.decode
    omega
  have hcallback : ∀ τ ∈ scales.1,∀ ρ ∈ revenues.1,
      (autoCandidate δ count capacity τ seeds.ratio alpha ρ fuel.1 products).2 ≤ C := by
    intro τ ht ρ hr
    have hh := autoCandidate_cost δ count capacity τ seeds.ratio alpha ρ fuel.1 products
      (hb.trans hGb) hδG hcount hcapG (hsBounds.2 τ ht).2 hratioG halphaG (hrBounds.2 ρ hr).2 hδv hδp hprodG
    exact hh.trans (autoCandidateCost_bound_mono hfLength)
  have hcross := cross_cost _ scales.1 revenues.1 hcallback
  have hcross' : cand.2 ≤ k*(k*(C+5)+5)+1 := by
    apply hcross.trans
    gcongr
    · exact hsBounds.1
    · exact hrBounds.1
  have hcLength : cand.1.length ≤ k^2 := by
    have hh := cross_length (fun τ ρ => autoCandidate δ count capacity τ seeds.ratio alpha ρ fuel.1 products) scales.1 revenues.1
    apply hh.trans
    rw [pow_two]
    exact Nat.mul_le_mul hsBounds.1 hrBounds.1
  have hcWidth : ∀ s ∈ cand.1,s.choices.length ≤ N ∧ ∀ x ∈ s.choices,x.Width W := by
    intro s hs
    obtain ⟨τ,ht,ρ,hr,hresult⟩ := cross_member hs
    have hh := autoCandidate_width hδG hcount (hsBounds.2 τ ht).2 hratioG halphaG (hrBounds.2 ρ hr).2 hδv hδp hprodG hresult
    change s.Width (FPTASCostKernel.kernelWidth N (FPTASCostOptions.groupWidth (4*G*(Q+1)) G)) ∧ s.choices.length ≤ N at hh
    refine ⟨hh.2, ?_⟩
    intro x hx
    exact KnapsackCostState.Fraction.width_mono (hh.1.2.2.2 x hx) (by dsimp [W]; omega)
  have hBW : b ≤ W := by dsimp [W]; omega
  have hprices : prices.length ≤ N ∧ ∀ x ∈ prices,x.Width W := by
    refine ⟨by simp [prices,N],?_⟩
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact KnapsackCostState.Fraction.width_mono (hprod p hp).1 hBW
  have hsingleton : ∀ xs ∈ singleton.1,xs.length ≤ N ∧ ∀ x ∈ xs,x.Width W := by
    intro xs hxs
    obtain ⟨hlen,hmem⟩ := singletons_shape values xs hxs
    refine ⟨by simpa [values,N] using hlen.le,?_⟩
    intro x hx
    rcases hmem x hx with rfl | hx
    · exact KnapsackCostState.Fraction.width_mono FPTASCostKernel.zero_width (hb.trans hBW)
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      exact KnapsackCostState.Fraction.width_mono (hprod p hp).2 hBW
  have hempty : empty.1.length ≤ N ∧ ∀ x ∈ empty.1,x.Width W := by
    refine ⟨by simp [empty,zeroes_eq,values,N],?_⟩
    intro x hx
    simp only [empty,zeroes_eq,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    exact KnapsackCostState.Fraction.width_mono FPTASCostKernel.zero_width (hb.trans hBW)
  have hcandidates : ∀ xs ∈ singleton.1++vectors,xs.length ≤ N ∧ ∀ x ∈ xs,x.Width W := by
    intro xs hxs
    rcases List.mem_append.mp hxs with hs | hs
    · exact hsingleton xs hs
    · change xs ∈ cand.1.map KnapsackCostState.State.choices at hs
      obtain ⟨s,hsm,heq⟩ := List.mem_map.mp hs
      rw [← heq]
      exact hcWidth s hsm
  have hupdate := improveAll_cost prices empty.1 (singleton.1++vectors)
    hprices.1 hempty.1 hprices.2 hempty.2 hcandidates
  have hsLength : singleton.1.length = N := by simp [singleton,singletons_count,values,N]
  have hvLength : vectors.length ≤ k^2 := by simpa [vectors] using hcLength
  have hupdate' : (improveAll prices empty.1 (singleton.1++vectors)).2 ≤ (N+k^2)*updateBudget N W+1 := by
    apply hupdate.trans
    unfold updateBudget
    gcongr
    simp only [List.length_append,hsLength]
    omega
  have hsCost' := singletons_cost values
  have heCost' := zeroes_cost values
  have hpCost := prepareSeeds_cost alpha epsilon products hb ha he hprod
  have hnCost := countBits_cost products
  have hvals : values.length = N := by simp [values,N]
  rw [hvals] at hsCost' heCost'
  change singleton.2 ≤ 8*N^2+8*N+1 at hsCost'
  change empty.2 = 4*N+1 at heCost'
  change prep.2 ≤ 256*(b+5)^2+8+64*(N+1)^2+3+seedCost N B+4 at hpCost
  change counted.2 ≤ 64*(N+1)^2+1 at hnCost
  change scales.2 ≤ gridBudget S Q at hsCost
  change revenues.2 ≤ gridBudget S Q at hrCost
  have hres : (improveAll prices empty.1 (singleton.1++vectors)).1.length ≤ N ∧
      ∀ x ∈ (improveAll prices empty.1 (singleton.1++vectors)).1,x.Width W := by
    rcases improveAll_member prices empty.1 (singleton.1++vectors) with heq | hm
    · simpa only [heq] using hempty
    · exact hcandidates _ hm
  rw [← hQ]
  constructor
  · change prep.2+counted.2+fuel.2+scales.2+revenues.2+cand.2+singleton.2+empty.2+
      (improveAll prices empty.1 (singleton.1++vectors)).2+2*N+cand.1.length+singleton.1.length+20 ≤ _
    unfold salesBudget
    change _ ≤ (256*(b+5)^2+8+64*(N+1)^2+3+seedCost N B+4)+64*(N+1)^2+1+
      (16384*(B+1)^2+2*(N^2*Q)+4*(5*B+2)+5)+2*gridBudget S Q+
      (k*(k*(C+5)+5)+1)+(8*N^2+8*N+1)+(4*N+1)+((N+k^2)*updateBudget N W+1)+3*N+k^2+20
    omega
  · change (improveAll prices empty.1 (singleton.1++vectors)).1.length ≤ N ∧
      ∀ x ∈ (improveAll prices empty.1 (singleton.1++vectors)).1,
        x.Width (salesOutputWidth b N Q)
    exact hres

theorem runSalesBits_cost (alpha epsilon capacity : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (he : epsilon.Width b) (hk : capacity.Width b)
    (hprod : ∀ p ∈ products,p.1.Width b ∧ p.2.Width b)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hep : 0 < epsilon.decode)
    (hprodv : ∀ p ∈ products,p.1.Valid ∧ p.2.Valid) (hne : products ≠ []) :
    (runSalesBits alpha epsilon capacity products).2 ≤
      salesBudget b products.length ⌈10/epsilon.decode⌉₊ :=
  (runSalesBits_analysis alpha epsilon capacity products hb ha he hk hprod hav hev hep hprodv hne).1

theorem runSalesBits_shape (alpha epsilon capacity : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (he : epsilon.Width b) (hk : capacity.Width b)
    (hprod : ∀ p ∈ products,p.1.Width b ∧ p.2.Width b)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hep : 0 < epsilon.decode)
    (hprodv : ∀ p ∈ products,p.1.Valid ∧ p.2.Valid) (hne : products ≠ []) :
    (runSalesBits alpha epsilon capacity products).1.length ≤ products.length ∧
    ∀ x ∈ (runSalesBits alpha epsilon capacity products).1,
      x.Width (salesOutputWidth b products.length ⌈10/epsilon.decode⌉₊) :=
  (runSalesBits_analysis alpha epsilon capacity products hb ha he hk hprod hav hev hep hprodv hne).2

end BalancedAssortments.FPTASCostProgram
