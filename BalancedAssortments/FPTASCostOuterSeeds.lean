import BalancedAssortments.FPTASCostSeedLists

/-! A single binary straight-line/list program constructs every outer grid seed.
Its polynomial cost includes extrema, singleton generation, and seed arithmetic. -/
namespace BalancedAssortments.FPTASCostSeeds
open KnapsackCostRational FPTASCostGrid

structure SeedPack where
  scaleBase : Fraction
  scaleCap : Fraction
  revenueBase : Fraction
  revenueCap : Fraction
  ratio : Fraction

def SeedPack.Valid (s : SeedPack) : Prop :=
  s.scaleBase.Valid ∧ s.scaleCap.Valid ∧ s.revenueBase.Valid ∧ s.revenueCap.Valid ∧ s.ratio.Valid

def SeedPack.Width (s : SeedPack) (b : ℕ) : Prop :=
  s.scaleBase.Width b ∧ s.scaleCap.Width b ∧ s.revenueBase.Width b ∧
    s.revenueCap.Width b ∧ s.ratio.Width b

def outerSeeds (alpha delta count initialAttraction : Fraction) (products : List Product) : SeedPack × ℕ :=
  let vs := products.map Prod.snd
  let rs := products.map Prod.fst
  let vmin := foldExtreme true initialAttraction vs
  let vmax := foldExtreme false zero vs
  let rmax := foldExtreme false zero rs
  let best := bestSingleton products
  let base := scaleBase alpha vmin.1 count
  let cap := multiplyFresh alpha vmax.1
  let ratio := KnapsackCostRational.add one delta
  (⟨base.1,cap.1,best.1,rmax.1,ratio.1⟩,
    vmin.2+vmax.2+rmax.2+best.2+base.2+cap.2+ratio.2+16*products.length+32)

lemma outerSeeds_valid (alpha delta count initial : Fraction) (products : List Product)
    (ha : alpha.Valid) (hd : delta.Valid) (hn : 0 < count.decode) (hi : initial.Valid)
    (hp : ∀ p ∈ products, p.1.Valid ∧ p.2.Valid) :
    (outerSeeds alpha delta count initial products).1.Valid := by
  have hv : ∀ v ∈ products.map Prod.snd, v.Valid := by
    intro v hv
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hv
    exact (hp p hp').2
  have hr : ∀ r ∈ products.map Prod.fst, r.Valid := by
    intro r hr
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hr
    exact (hp p hp').1
  exact ⟨scaleBase_valid ha (foldExtreme_valid true initial _ hi hv) hn,
    multiplyFresh_valid ha (foldExtreme_valid false zero _ zero_valid hv),
    bestSingleton_valid products hp, foldExtreme_valid false zero _ zero_valid hr,
    add_valid one_valid hd⟩

lemma outerSeeds_decode (alpha delta count initial : Fraction) (products : List Product)
    (hd : delta.Valid) (hi : initial.Valid)
    (hp : ∀ p ∈ products, p.1.Valid ∧ p.2.Valid) :
    let out := (outerSeeds alpha delta count initial products).1
    out.scaleBase.decode = alpha.decode *
      ((products.map fun p => p.2.decode).foldl min initial.decode) / count.decode ∧
    out.scaleCap.decode = alpha.decode * FPTAS.maxList (products.map fun p => p.2.decode) ∧
    out.revenueBase.decode = FPTAS.maxList (products.map fun p => p.1.decode*p.2.decode/(1+p.2.decode)) ∧
    out.revenueCap.decode = FPTAS.maxList (products.map fun p => p.1.decode) ∧
    out.ratio.decode = 1+delta.decode := by
  have hv : ∀ v ∈ products.map Prod.snd, v.Valid := by
    intro v hv
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hv
    exact (hp p hp').2
  have hr : ∀ r ∈ products.map Prod.fst, r.Valid := by
    intro r hr
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hr
    exact (hp p hp').1
  have hmin := foldExtreme_decode true initial _ hi hv
  have hmax := foldExtreme_decode false zero _ zero_valid hv
  have hrmax := foldExtreme_decode false zero _ zero_valid hr
  simp only [List.map_map, Function.comp_def, extremum, ↓reduceIte, zero_decode] at hmin hmax hrmax
  dsimp only [outerSeeds]
  refine ⟨?_, ?_, bestSingleton_decode products hp, hrmax, ?_⟩
  · rw [scaleBase_decode, hmin]
    rfl
  · rw [multiplyFresh_decode, hmax]
    rfl
  · rw [add_decode one_valid hd, one_decode]

lemma outerSeeds_width (alpha delta count initial : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (hd : delta.Width b) (hn : count.Width b) (hi : initial.Width b)
    (hp : ∀ p ∈ products, p.1.Width b ∧ p.2.Width b) :
    (outerSeeds alpha delta count initial products).1.Width (7*b+4) := by
  have hv : ∀ v ∈ products.map Prod.snd, v.Width b := by
    intro v hv
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hv
    exact (hp p hp').2
  have hr : ∀ r ∈ products.map Prod.fst, r.Width b := by
    intro r hr
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hr
    exact (hp p hp').1
  have hmin := foldExtreme_width true initial _ hi hv
  have hmax := foldExtreme_width false zero _ (zero_width hb) hv
  have hrmax := foldExtreme_width false zero _ (zero_width hb) hr
  have hbase := scaleBase_width ha hmin hn
  have hcap := multiplyFresh_width ha hmax
  have hratio := add_width one_width hd
  refine ⟨?_, ?_, bestSingleton_width products hp, ?_, ?_⟩
  · exact ⟨hbase.1.trans (by omega), hbase.2.trans (by omega)⟩
  · exact ⟨hcap.1.trans (by omega), hcap.2.trans (by omega)⟩
  · exact ⟨hrmax.1.trans (by omega), hrmax.2.trans (by omega)⟩
  · exact ⟨hratio.1.trans (by omega), hratio.2.trans (by omega)⟩

/-- A polynomial using only +, *, and fixed natural powers. -/
def seedCost (m b : ℕ) : ℕ :=
  3*(m*(512*(b+1)^2+10)+1) +
  (m*(32768*(b+1)^2+36)+m*(512*(7*b+5)^2+10)+6) +
  (8192*(b+1)^2+32)+(256*(b+b+1)^2+6)+256*(1+b+1)^2+16*m+32

theorem outerSeeds_cost (alpha delta count initial : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (hd : delta.Width b) (hn : count.Width b) (hi : initial.Width b)
    (hp : ∀ p ∈ products, p.1.Width b ∧ p.2.Width b) :
    (outerSeeds alpha delta count initial products).2 ≤ seedCost products.length b := by
  have hv : ∀ v ∈ products.map Prod.snd, v.Width b := by
    intro v hv
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hv
    exact (hp p hp').2
  have hr : ∀ r ∈ products.map Prod.fst, r.Width b := by
    intro r hr
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hr
    exact (hp p hp').1
  have hmin := foldExtreme_cost true initial _ hi hv
  have hmax := foldExtreme_cost false zero _ (zero_width hb) hv
  have hrmax := foldExtreme_cost false zero _ (zero_width hb) hr
  simp only [List.length_map] at hmin hmax hrmax
  have hbest := bestSingleton_cost products hp
  have hbase := scaleBase_cost ha (foldExtreme_width true initial _ hi hv) hn
  have hcap := multiplyFresh_cost ha (foldExtreme_width false zero _ (zero_width hb) hv)
  have hratio := add_cost one_width hd
  dsimp only [outerSeeds, seedCost]
  omega

end BalancedAssortments.FPTASCostSeeds
