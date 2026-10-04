import BalancedAssortments.FPTASCostProgramSeeds
import BalancedAssortments.FPTASCostAutoCandidateLength
import BalancedAssortments.FPTASCostFunctional

namespace BalancedAssortments.FPTASCostProgram
open KnapsackCostRational FPTASCostSeeds FPTASCostGrid FPTASCostLoops FPTASCostSingletons
open FPTASCostCandidate FPTASCostFunctional FPTAS

def programStates {n : ℕ} (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product) :=
  (cross (fun τ ρ => autoCandidate (programDelta alpha epsilon rv) (programCount rv) capacity τ
    (programSeeds alpha epsilon rv).ratio alpha ρ (programFuel alpha epsilon rv) (sourceProducts rv))
    (programScales alpha epsilon rv) (programRevenues alpha epsilon rv)).1

def programValues {n : ℕ} (rv : Fin (n+1) → Product) := (sourceProducts rv).map Prod.snd
def programPrices {n : ℕ} (rv : Fin (n+1) → Product) := (sourceProducts rv).map Prod.fst

def programVectors {n : ℕ} (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product) :=
  (singletons (programValues rv)).1 ++
    (programStates alpha epsilon capacity rv).map KnapsackCostState.State.choices

theorem programStates_decode {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (had : alpha.decode = d.α)
    (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (hf : ProgramSeedFacts d ε alpha epsilon capacity rv) :
    (programStates alpha epsilon capacity rv).map (fun s => FPTAS.stateVector (n := n) s.decode) =
      (scales d (ε/10)).flatMap (fun τ => (revenues d (ε/10)).filterMap (candidateAt d (ε/10) τ)) := by
  have hb : (programFuel alpha epsilon rv).length =
      (n+1)*⌈(n+1 : ℚ)/(programDelta alpha epsilon rv).decode⌉₊ := by
    rw [hf.delta_decode]; exact hf.fuel_length
  have hh := cross_refinement
    (fun τ ρ => autoCandidate (programDelta alpha epsilon rv) (programCount rv) capacity τ
      (programSeeds alpha epsilon rv).ratio alpha ρ (programFuel alpha epsilon rv) (sourceProducts rv))
    Fraction.decode Fraction.decode (fun s => FPTAS.stateVector (n := n) s.decode)
    (candidateAt d (programDelta alpha epsilon rv).decode)
    (programScales alpha epsilon rv) (programRevenues alpha epsilon rv) (by
      intro τ hτ ρ hρ
      exact autoCandidate_decode d _ _ _ τ _ alpha ρ _ rv
        hf.delta_valid hf.delta_positive hf.count_decode hf.capacity_valid hf.capacity_decode
        (hf.scales_valid_positive τ hτ).1 hf.seeds_valid.2.2.2.2 ha
        (hf.revenues_valid_positive ρ hρ).1 hprod hdec had hf.ratio_decode
        (hf.scales_valid_positive τ hτ).2 hd.2.1 (fun i => (hd.1 i).2) hb)
  simpa only [programStates,hf.scales_decode,hf.revenues_decode,hf.delta_decode] using hh

def rationalVector {n : ℕ} (xs : List ℚ) : Fin n → ℚ := fun i => xs[i.val]?.getD 0

lemma rationalVector_ofFn {n : ℕ} (f : Fin n → ℚ) : rationalVector (List.ofFn f) = f := by
  funext i; simp [rationalVector]

lemma rationalVector_decode {n : ℕ} (xs : List Fraction) :
    rationalVector (n := n) (xs.map Fraction.decode) = decodeVector xs := by
  funext i; simp [rationalVector,decodeVector,List.getElem?_map]

theorem programSingletons_decode {n : ℕ} (d : Input n) (rv : Fin (n+1) → Product)
    (hdec : ∀ i,(rv i).2.decode = d.v i) :
    ((singletons (programValues rv)).1.map (decodeVector (n := n+1))) =
      (List.finRange (n+1)).map (singleton d) := by
  have hvals : (programValues rv).map Fraction.decode = List.ofFn d.v := by
    simp only [programValues,sourceProducts,List.map_map,Function.comp_def]
    rw [List.ofFn_eq_map]
    exact List.map_congr_left (fun i _ => hdec i)
  have hh := congrArg (List.map (rationalVector (n := n+1))) (singletons_decode (programValues rv))
  rw [hvals,rationalSingletons_ofFn,List.map_ofFn] at hh
  simp only [List.map_map,Function.comp_def,rationalVector_decode,rationalVector_ofFn] at hh
  simpa only [List.ofFn_eq_map,FPTAS.singleton] using hh

theorem programVectors_decode {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (had : alpha.decode = d.α)
    (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (hf : ProgramSeedFacts d ε alpha epsilon capacity rv) :
    (programVectors alpha epsilon capacity rv).map (decodeVector (n := n+1)) = rawCandidates d ε := by
  unfold programVectors rawCandidates
  rw [List.map_append,programSingletons_decode d rv (fun i => (hdec i).2)]
  simp only [List.map_map,Function.comp_def]
  have hh := programStates_decode d hd ε alpha epsilon capacity rv ha had hprod hdec hf
  simpa only [stateVector_decode] using congrArg
    (fun tail => (List.finRange (n+1)).map (singleton d) ++ tail) hh

theorem programVectors_shape {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product)
    (had : alpha.decode = d.α)
    (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).2.decode = d.v i)
    (hf : ProgramSeedFacts d ε alpha epsilon capacity rv) :
    ∀ xs ∈ programVectors alpha epsilon capacity rv,
      xs.length = n+1 ∧ ∀ x ∈ xs, x.Valid := by
  intro xs hxs
  simp only [programVectors,List.mem_append] at hxs
  have hvals : ∀ x ∈ programValues rv, x.Valid := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact (hf.products_valid p hp).2
  rcases hxs with hs | hs
  · have hh := singletons_shape (programValues rv) xs hs
    refine ⟨by simpa [programValues,sourceProducts] using hh.1, ?_⟩
    intro x hx
    rcases hh.2 x hx with rfl | hx
    · exact FPTASCostKernel.zero_valid
    · exact hvals x hx
  · obtain ⟨s,hsmem,rfl⟩ := List.mem_map.mp hs
    obtain ⟨τ,hτ,ρ,hρ,hcall⟩ := cross_member hsmem
    have hvp : ∀ p ∈ sourceProducts rv, p.1.Valid ∧ 0 < p.2.decode := by
      intro p hp
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
      exact ⟨(hprod i).1,by rw [hdec i]; exact (hd.1 i).2⟩
    have hvalid := autoCandidate_valid (hf.scales_valid_positive τ hτ).1
      hf.seeds_valid.2.2.2.2 (hf.revenues_valid_positive ρ hρ).1
      (by rw [had]; exact hd.2.1) hvp hcall
    have hlen := autoCandidate_choices_length hcall
    exact ⟨by simpa [sourceProducts] using hlen,hvalid.2.2⟩


theorem programPrices_vector {n : ℕ} (d : Input n) (rv : Fin (n+1) → Product)
    (hdec : ∀ i,(rv i).1.decode = d.r i) : decodeVector (programPrices rv) = d.r := by
  have he : programPrices rv = List.ofFn (fun i => (rv i).1) := by
    simp only [programPrices,sourceProducts,List.ofFn_eq_map,List.map_map,Function.comp_def]
  rw [he,decodeVector_ofFn]
  funext i
  exact hdec i

theorem programZero_vector {n : ℕ} (rv : Fin (n+1) → Product) :
    decodeVector (n := n+1) (zeroes (programValues rv)).1 = fun _ => 0 := by
  funext i
  simp [decodeVector,zeroes_eq,programValues,sourceProducts,FPTASCostKernel.zero_decode,i.isLt]

theorem programRevenue_decode {n : ℕ} (d : Input n) (rv : Fin (n+1) → Product)
    (hprod : ∀ i,(rv i).1.Valid) (hdec : ∀ i,(rv i).1.decode = d.r i)
    (xs : List Fraction) (hlen : xs.length = n+1) (hv : ∀ x ∈ xs,x.Valid) :
    (FPTASCostOutput.revenue (programPrices rv) xs).1.decode = FPTAS.revenue d (decodeVector xs) := by
  have hp : ∀ x ∈ programPrices rv,x.Valid := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact hprod i
  rw [list_revenue_fin _ _ (by simp [programPrices,sourceProducts]) hlen hp hv,
    programPrices_vector d rv hdec]
  rfl

/-- Actual raw binary output is a feasible complete product vector and its
unrounded revenue dominates the already proved source algorithm. -/
theorem runSalesBits_semantics {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ) (hε : 0 < ε)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hcv : capacity.Valid)
    (had : alpha.decode = d.α) (hed : epsilon.decode = ε) (hcd : capacity.decode = d.K)
    (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i) :
    let out := (runSalesBits alpha epsilon capacity (sourceProducts rv)).1
    out.length = n+1 ∧ (∀ x ∈ out,x.Valid) ∧ Feasible d (decodeVector out) ∧
      FPTAS.revenue d (FPTAS.runSales d ε) ≤ FPTAS.revenue d (decodeVector out) := by
  let old := (zeroes (programValues rv)).1
  let cs := programVectors alpha epsilon capacity rv
  let out := (improveAll (programPrices rv) old cs).1
  have hf := programSeedFacts d hd ε hε alpha epsilon capacity rv hav hev hcv had hed hcd
    hprod (fun i => (hdec i).1) (fun i => (hdec i).2)
  have hshape := programVectors_shape d hd ε alpha epsilon capacity rv had hprod (fun i => (hdec i).2) hf
  have hdecode := programVectors_decode d hd ε alpha epsilon capacity rv hav had hprod hdec hf
  have holdlen : old.length = n+1 := by simp [old,zeroes_eq,programValues,sourceProducts]
  have holdvalid : ∀ x ∈ old,x.Valid := by
    intro x hx
    simp only [old,zeroes_eq,List.mem_replicate] at hx
    rw [hx.2]
    exact FPTASCostKernel.zero_valid
  have hprices : ∀ x ∈ programPrices rv,x.Valid := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact (hf.products_valid p hp).1
  have hmember := improveAll_member (programPrices rv) old cs
  have hout : out.length = n+1 ∧ (∀ x ∈ out,x.Valid) ∧ Feasible d (decodeVector out) := by
    rcases hmember with ho | ho
    · change out = old at ho
      rw [ho]
      refine ⟨holdlen,holdvalid,?_⟩
      rw [show decodeVector (n := n+1) old = fun _ => 0 from programZero_vector rv]
      exact zero_feasible d (fun i => (hd.1 i).2.le)
    · refine ⟨(hshape out ho).1,(hshape out ho).2,?_⟩
      apply rawCandidates_feasible d hd hε.le
      rw [←hdecode]
      exact List.mem_map.mpr ⟨out,ho,rfl⟩
  have hsource : FPTAS.runSales d ε ∈ cs.map (decodeVector (n := n+1)) := by
    rw [hdecode]
    exact runSales_mem_raw d hd hε.le
  obtain ⟨xs,hxs,hxeq⟩ := List.mem_map.mp hsource
  have hmax := improveAll_max (programPrices rv) old cs hprices holdvalid
    (fun xs hx => (hshape xs hx).2)
  have hh := le_fold_max_member (cs.map fun xs => (FPTASCostOutput.revenue (programPrices rv) xs).1.decode)
    (List.mem_map.mpr ⟨xs,hxs,rfl⟩) (FPTASCostOutput.revenue (programPrices rv) old).1.decode
  rw [←hmax] at hh
  change (FPTASCostOutput.revenue (programPrices rv) xs).1.decode ≤
    (FPTASCostOutput.revenue (programPrices rv) out).1.decode at hh
  rw [programRevenue_decode d rv (fun i => (hprod i).1) (fun i => (hdec i).1)
        xs (hshape xs hxs).1 (hshape xs hxs).2,
      programRevenue_decode d rv (fun i => (hprod i).1) (fun i => (hdec i).1)
        out hout.1 hout.2.1,hxeq] at hh
  exact ⟨hout.1,hout.2.1,hout.2.2,hh⟩

/-- End-to-end mathematical approximation for the actual fully binary sales
program, against arbitrary feasible REAL sales vectors. -/
theorem runSalesBits_approximation {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hcv : capacity.Valid)
    (had : alpha.decode = d.α) (hed : epsilon.decode = ε) (hcd : capacity.decode = d.K)
    (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (u : Fin (n+1) → ℝ)
    (hu : Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K u) :
    (1-(ε:ℝ))*Optimization.revenue (fun i => (d.r i : ℝ)) u ≤
      (FPTAS.revenue d (decodeVector (runSalesBits alpha epsilon capacity (sourceProducts rv)).1) : ℝ) := by
  have hs := runSalesBits_semantics d hd ε hε alpha epsilon capacity rv hav hev hcv had hed hcd hprod hdec
  have hm : (FPTAS.revenue d (FPTAS.runSales d ε) : ℝ) ≤
      (FPTAS.revenue d (decodeVector (runSalesBits alpha epsilon capacity (sourceProducts rv)).1) : ℝ) := by
    exact_mod_cast hs.2.2.2
  exact (FPTAS.runSales_approximation d hd ε hε hε1 u hu).trans hm
end BalancedAssortments.FPTASCostProgram
