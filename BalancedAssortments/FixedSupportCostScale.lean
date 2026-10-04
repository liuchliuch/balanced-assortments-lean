import BalancedAssortments.FixedSupportCostScalars
import BalancedAssortments.FPTASCostInputSeeds

namespace BalancedAssortments.FixedSupportCostScale
open ComplexityTimeFractions (decode Valid width zero one zero_valid one_valid zero_decode one_decode)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars

def scaleUpperBits (K : Fraction) (vs : List Fraction) : Fraction × ℕ :=
  let s := inverseSumBits vs
  let q := divideFresh K s.1
  let out := foldExtreme true q.1 vs
  (out.1,s.2+q.2+out.2+4)

theorem scaleUpperBits_valid (K : Fraction) (vs : List Fraction) (hK : Valid K)
    (hv : ∀ v ∈ vs,Valid v) : Valid (scaleUpperBits K vs).1 :=
  foldExtreme_valid true _ vs (divideFresh_valid _ _ hK (inverseSumBits_valid vs)) hv

theorem scaleUpperBits_decode (K : Fraction) (vs : List Fraction) (hK : Valid K)
    (hv : ∀ v ∈ vs,Valid v) :
    decode (scaleUpperBits K vs).1 = (vs.map decode).foldl min
      (decode K/(vs.map (fun v => 1/decode v)).sum) := by
  simp only [scaleUpperBits,foldExtreme_decode _ _ _
    (divideFresh_valid _ _ hK (inverseSumBits_valid vs)) hv,
    divideFresh_decode,inverseSumBits_decode]
  rfl

def upperWidth (n B : ℕ) : ℕ := B+2*inverseWidth n B+1
def upperCost (n B : ℕ) : ℕ := inverseCost n B+
  (1024*(B+inverseWidth n B+2)^2+64*inverseWidth n B+34)+
  (n*(2048*(2*upperWidth n B+1)^2+6)+1)+4

theorem scaleUpperBits_bounds (K : Fraction) (vs : List Fraction) {B : ℕ}
    (hK : Valid K) (hv : ∀ v ∈ vs,Valid v) (hKw : width K≤B) (hvw : ∀ v ∈ vs,width v≤B) :
    width (scaleUpperBits K vs).1 ≤ upperWidth vs.length B ∧
      (scaleUpperBits K vs).2 ≤ upperCost vs.length B := by
  have hs := inverseSumBits_width vs hv hvw
  have hsc := inverseSumBits_cost vs hv hvw
  have hq := divideFresh_width_valid hKw hs (inverseSumBits_valid vs)
  have hqc := divideFresh_cost hKw hs
  have hvs : ∀ v ∈ vs,width v≤upperWidth vs.length B := fun v hm => (hvw v hm).trans (by unfold upperWidth;omega)
  have hout := foldExtreme_width_cost true (divideFresh K (inverseSumBits vs).1).1 vs hq hvs
  refine ⟨hout.1,?_⟩
  dsimp only [scaleUpperBits,upperCost]
  dsimp only [upperWidth] at *
  omega

private theorem filter_decode (upper : Fraction) (xs : List Fraction)
    (hu : Valid upper) (hx : ∀ x ∈ xs,Valid x) :
    ((filterCost (within upper) xs).1.map decode) =
      (xs.map decode).filter (fun t => decide (0≤t ∧ t≤decode upper)) := by
  rw [filterCost_value,List.filter_map]
  apply congrArg (List.map decode)
  apply List.filter_congr
  intro x hm
  apply Bool.eq_iff_iff.mpr
  simpa using within_correct upper x hu (hx x hm)

def capCutBits (α T : Fraction) (vs : List Fraction) : List Fraction × ℕ :=
  let products := mapCost (multiplyFresh α) vs
  let filtered := filterCost (within T) products.1
  (zero::T::filtered.1,products.2+filtered.2+6)

theorem capCutBits_valid (α T : Fraction) (vs : List Fraction)
    (hα : Valid α) (hT : Valid T) (hv : ∀ v ∈ vs,Valid v) :
    ∀ x ∈ (capCutBits α T vs).1,Valid x := by
  intro x hx
  simp only [capCutBits,List.mem_cons,filterCost_value] at hx
  rcases hx with rfl | rfl | hx
  · exact zero_valid
  · exact hT
  · have hm := List.mem_of_mem_filter hx
    rw [mapCost_value] at hm
    obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hm
    exact multiplyFresh_valid _ _ hα (hv v hv')

theorem capCutBits_decode (α T : Fraction) (vs : List Fraction)
    (hα : Valid α) (hT : Valid T) (hv : ∀ v ∈ vs,Valid v) :
    (capCutBits α T vs).1.map decode = 0::decode T::
      ((vs.map (fun v => decode α*decode v)).filter (fun t => decide (0≤t ∧ t≤decode T))) := by
  have hp : ∀ x ∈ (mapCost (multiplyFresh α) vs).1,Valid x := by
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hx
    exact multiplyFresh_valid _ _ hα (hv v hv')
  simp only [capCutBits,List.map_cons,zero_decode]
  rw [filter_decode T _ hT hp]
  simp [mapCost_value,List.map_map,Function.comp_def,multiplyFresh_decode]

theorem capCutBits_length (α T : Fraction) (vs : List Fraction) :
    (capCutBits α T vs).1.length ≤ vs.length+2 := by
  have hh := List.length_filter_le (fun x => (within T x).1) (mapCost (multiplyFresh α) vs).1
  simp only [mapCost_length] at hh
  simp only [capCutBits,List.length_cons,filterCost_value]
  omega

def cutsCost (n B : ℕ) : ℕ := n*(1024*(2*B+1)^2+4)+1 +
  (n*(32768*(3*B+3)^2+5)+1)+6

theorem capCutBits_bounds (α T : Fraction) (vs : List Fraction) {B : ℕ}
    (hα : width α≤B) (hT : width T≤B) (hv : ∀ v ∈ vs,width v≤B) :
    (∀ x ∈ (capCutBits α T vs).1,width x≤3*B+2) ∧
      (capCutBits α T vs).2 ≤ cutsCost vs.length B := by
  have hw : ∀ x ∈ (mapCost (multiplyFresh α) vs).1,width x≤3*B+2 := by
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hx
    have hh := multiplyFresh_width hα (hv v hv')
    omega
  have hp := mapCost_cost (multiplyFresh α) vs (fun v hv' => multiplyFresh_cost hα (hv v hv'))
  have ht : width T≤3*B+2 := by omega
  have hf := filterCost_cost (within T) (mapCost (multiplyFresh α) vs).1
    (fun x hx => within_cost T x ht (hw x hx))
  constructor
  · intro x hx
    simp only [capCutBits,List.mem_cons,filterCost_value] at hx
    rcases hx with rfl | rfl | hx
    · simp
    · exact ht
    · exact hw x (List.mem_of_mem_filter hx)
  · simp only [mapCost_length] at hf
    dsimp only [capCutBits,cutsCost]
    nlinarith

/-- The cutoff test used to split capped and uncapped prefix coordinates. -/
def capped (α cut v : Fraction) : Bool × ℕ :=
  let p := multiplyFresh α v
  let c := FixedSupportCostRational.le p.1 cut
  (c.1,p.2+c.2+4)

theorem capped_correct (α cut v : Fraction) (hα : Valid α) (hc : Valid cut) (hv : Valid v) :
    (capped α cut v).1=true ↔ decode α*decode v≤decode cut := by
  simp only [capped,le_correct _ _ (multiplyFresh_valid _ _ hα hv) hc,multiplyFresh_decode]

theorem capped_cost (α cut v : Fraction) {B : ℕ} (hα : width α≤B)
    (hc : width cut≤B) (hv : width v≤B) : (capped α cut v).2 ≤ 65536*(B+1)^2 := by
  have hp := multiplyFresh_cost hα hv
  have hw := multiplyFresh_width hα hv
  have hl := le_cost hw hc
  dsimp only [capped]
  nlinarith

def countFraction (xs : List Fraction) : Fraction × ℕ :=
  let c := FPTASCostSeeds.countBits xs
  (⟨(c.1,[]),[true]⟩,c.2+2)

@[simp] theorem countFraction_valid (xs : List Fraction) : Valid (countFraction xs).1 := by
  norm_num [countFraction,Valid,ComplexityTimeBinary.value]

@[simp] theorem countFraction_decode (xs : List Fraction) : decode (countFraction xs).1 = xs.length := by
  simp [countFraction,decode,ComplexityTimeVerifier.zvalue,FPTASCostSeeds.countBits_value,ComplexityTimeBinary.value]

theorem countFraction_width (xs : List Fraction) : width (countFraction xs).1 ≤ xs.length+1 := by
  have hh := FPTASCostSeeds.countBits_width xs
  simpa [countFraction,width,ComplexityTimeVerifier.width] using hh

theorem countFraction_cost (xs : List Fraction) : (countFraction xs).2 ≤ 64*(xs.length+1)^2+3 := by
  exact Nat.add_le_add_right (FPTASCostSeeds.countBits_cost xs) 2

def prefixRootBits (α K cut : Fraction) (prefixVs suffixVs : List Fraction) : Fraction × ℕ :=
  let cs := filterCost (capped α cut) prefixVs
  let us := filterCost (fun v => let c := capped α cut v; (!c.1,c.2+1)) prefixVs
  let count := countFraction cs.1
  let top := subtractFresh K count.1
  let si := inverseSumBits suffixVs
  let ui := inverseSumBits us.1
  let ia := reciprocal α
  let term := multiplyFresh ui.1 ia.1
  let bot := addFresh si.1 term.1
  let out := divideFresh top.1 bot.1
  (out.1,cs.2+us.2+count.2+top.2+si.2+ui.2+ia.2+term.2+bot.2+out.2+16)

theorem prefixRootBits_valid (α K cut : Fraction) (ps ss : List Fraction)
    (hK : Valid K) : Valid (prefixRootBits α K cut ps ss).1 := by
  apply divideFresh_valid
  · exact subtractFresh_valid _ _ hK (countFraction_valid _)
  · exact addFresh_valid _ _ (inverseSumBits_valid _) (multiplyFresh_valid _ _
      (inverseSumBits_valid _) (reciprocal_valid _))

theorem prefixRootBits_decode (α K cut : Fraction) (ps ss : List Fraction)
    (hα : Valid α) (hK : Valid K) (hc : Valid cut) (hp : ∀ v ∈ ps,Valid v) :
    decode (prefixRootBits α K cut ps ss).1 =
      (decode K - ((ps.filter (fun v => decide (decode α*decode v≤decode cut))).length : ℚ)) /
      ((ss.map (fun v => 1/decode v)).sum + (1/decode α)*
        ((ps.filter (fun v => decide (¬decode α*decode v≤decode cut))).map
          (fun v => 1/decode v)).sum) := by
  have hcs : (filterCost (capped α cut) ps).1 =
      ps.filter (fun v => decide (decode α*decode v≤decode cut)) := by
    rw [filterCost_value]
    apply List.filter_congr
    intro v hm
    apply Bool.eq_iff_iff.mpr
    simpa using capped_correct α cut v hα hc (hp v hm)
  have hus : (filterCost (fun v => let c := capped α cut v; (!c.1,c.2+1)) ps).1 =
      ps.filter (fun v => decide (¬decode α*decode v≤decode cut)) := by
    rw [filterCost_value]
    apply List.filter_congr
    intro v hm
    apply Bool.eq_iff_iff.mpr
    have hh := capped_correct α cut v hα hc (hp v hm)
    cases h : (capped α cut v).1 <;> simp_all
  simp only [prefixRootBits,divideFresh_decode,
    subtractFresh_decode _ _ hK (countFraction_valid _),
    addFresh_decode _ _ (inverseSumBits_valid _) (multiplyFresh_valid _ _
      (inverseSumBits_valid _) (reciprocal_valid _)),
    multiplyFresh_decode,reciprocal_decode,inverseSumBits_decode,countFraction_decode,hcs,hus]
  ring

def rootTopWidth (n B : ℕ) := B+2*(n+1)+2
def rootBottomWidth (n B : ℕ) := 3*inverseWidth n B+4*B+4
def rootWidth (n B : ℕ) := rootTopWidth n B+2*rootBottomWidth n B+1
def rootCost (n B : ℕ) :=
  (n*(65536*(B+1)^2+5)+1)+(n*(65536*(B+1)^2+6)+1)+
  (64*(n+1)^2+3)+(4096*(B+(n+1)+1)^2+2)+
  2*inverseCost n B+(64*B+32)+
  1024*(inverseWidth n B+B+1)^2+
  4096*(inverseWidth n B+(inverseWidth n B+2*B+1)+1)^2+
  (1024*(rootTopWidth n B+rootBottomWidth n B+2)^2+64*rootBottomWidth n B+34)+16

set_option maxHeartbeats 1200000 in
theorem prefixRootBits_bounds (α K cut : Fraction) (ps ss : List Fraction) {n B : ℕ}
    (hα : Valid α) (hp : ∀ v ∈ ps,Valid v) (hs : ∀ v ∈ ss,Valid v)
    (hαw : width α≤B) (hKw : width K≤B) (hcw : width cut≤B)
    (hpw : ∀ v ∈ ps,width v≤B) (hsw : ∀ v ∈ ss,width v≤B)
    (hpn : ps.length≤n) (hsn : ss.length≤n) :
    width (prefixRootBits α K cut ps ss).1 ≤ rootWidth n B ∧
      (prefixRootBits α K cut ps ss).2 ≤ rootCost n B := by
  let cs := (filterCost (capped α cut) ps).1
  let us := (filterCost (fun v => let c := capped α cut v; (!c.1,c.2+1)) ps).1
  have hcn : cs.length≤n := by
    apply le_trans _ hpn
    simpa [cs,filterCost_value] using (List.length_filter_le (fun v => (capped α cut v).1) ps)
  have hun : us.length≤n := by
    apply le_trans _ hpn
    simpa [us,filterCost_value] using (List.length_filter_le (fun v => !(capped α cut v).1) ps)
  have hu : ∀ v ∈ us,Valid v := by
    intro v hv
    simp only [us,filterCost_value,List.mem_filter] at hv
    exact hp v hv.1
  have huw : ∀ v ∈ us,width v≤B := by
    intro v hv
    simp only [us,filterCost_value,List.mem_filter] at hv
    exact hpw v hv.1
  have iw {xs : List Fraction} (hx : ∀ v ∈ xs,Valid v) (hxw : ∀ v ∈ xs,width v≤B)
      (hxn : xs.length≤n) : width (inverseSumBits xs).1≤ inverseWidth n B := by
    apply (inverseSumBits_width xs hx hxw).trans
    unfold inverseWidth
    gcongr
  have ic {xs : List Fraction} (hx : ∀ v ∈ xs,Valid v) (hxw : ∀ v ∈ xs,width v≤B)
      (hxn : xs.length≤n) : (inverseSumBits xs).2≤ inverseCost n B := by
    apply (inverseSumBits_cost xs hx hxw).trans
    unfold inverseCost
    gcongr
  have hsi := iw hs hsw hsn
  have hui := iw hu huw hun
  have hsic := ic hs hsw hsn
  have huic := ic hu huw hun
  have hcountw : width (countFraction cs).1≤n+1 := (countFraction_width cs).trans (by omega)
  have hcc : (countFraction cs).2≤64*(n+1)^2+3 := (countFraction_cost cs).trans (by gcongr)
  have htw := subtractFresh_width hKw hcountw
  have htc := subtractFresh_cost hKw hcountw
  have hai := (reciprocal_width α hα).trans hαw
  have haic : (reciprocal α).2≤64*B+32 := (reciprocal_cost α).trans (by omega)
  have hmw := multiplyFresh_width hui hai
  have hmc := multiplyFresh_cost hui hai
  have hbw := addFresh_width hsi hmw
  have hbc := addFresh_cost hsi hmw
  have hbv := addFresh_valid _ _ (inverseSumBits_valid ss)
    (multiplyFresh_valid _ _ (inverseSumBits_valid us) (reciprocal_valid α))
  have hbw' : width (addFresh (inverseSumBits ss).1
      (multiplyFresh (inverseSumBits us).1 (reciprocal α).1).1).1 ≤ rootBottomWidth n B := by
    unfold rootBottomWidth
    omega
  have htw' : width (subtractFresh K (countFraction cs).1).1≤rootTopWidth n B := htw
  have how := divideFresh_width_valid htw' hbw' hbv
  have hoc := divideFresh_cost htw' hbw'
  have hcf := filterCost_cost (capped α cut) ps (fun v hv => capped_cost α cut v hαw hcw (hpw v hv))
  have huf := filterCost_cost (fun v => let c := capped α cut v; (!c.1,c.2+1)) ps
    (fun v hv => Nat.add_le_add_right (capped_cost α cut v hαw hcw (hpw v hv)) 1)
  have hcf' : (filterCost (capped α cut) ps).2≤n*(65536*(B+1)^2+5)+1 := hcf.trans (by gcongr)
  have huf' : (filterCost (fun v => let c := capped α cut v; (!c.1,c.2+1)) ps).2≤n*(65536*(B+1)^2+6)+1 := by
    apply huf.trans
    gcongr
  constructor
  · exact how
  · change _ ≤ rootCost n B
    dsimp only [prefixRootBits]
    dsimp only [cs,us] at *
    unfold rootCost
    omega

end BalancedAssortments.FixedSupportCostScale
