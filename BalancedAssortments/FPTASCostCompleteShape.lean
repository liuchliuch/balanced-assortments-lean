import BalancedAssortments.FPTASCostCompleteBound

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace BalancedAssortments.FPTASCostComplete
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram Decomposition.CostMachine

private theorem marginalBits_valid (ws vs : List Fraction)
    (hw : ∀ w ∈ ws,w.Valid) (hv : ∀ v ∈ vs,0<v.decode) :
    ∀ z ∈ (marginalBits ws vs).1,z.Valid := by
  induction ws generalizing vs with
  | nil => simp [marginalBits]
  | cons w ws ih =>
    cases vs with
    | nil => simp [marginalBits]
    | cons v vs =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact divideFresh_valid (hw w (by simp)) (hv v (by simp))
      · exact ih _ (fun x hx => hw x (by simp [hx])) (fun x hx => hv x (by simp [hx])) z hz

private theorem product_denominator_positive (ms : List Fraction) (hm : ∀ m ∈ ms,m.Valid) :
    0 < value (productBits (ms.map Fraction.denominator)).1 := by
  rw [productBits_value]
  induction ms with
  | nil => simp
  | cons m ms ih =>
    have hhead := hm m (by simp)
    have htail := ih (fun x hx => hm x (by simp [hx]))
    simp only [List.map_cons,List.prod_cons]
    exact Nat.mul_pos hhead htail

private theorem tiltAtoms_valid_all (vs : List Fraction) (normalizer : Fraction)
    (as : List PolicyAtom) (hv : ∀ v ∈ vs,v.Valid) (hn : 0<normalizer.decode)
    (ha : ∀ a ∈ as,a.1.Valid) : ∀ a ∈ (tiltAtoms vs normalizer as).1,a.1.Valid := by
  induction as with
  | nil => simp [tiltAtoms]
  | cons a as ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact reverseWeight_valid vs a.2 hv (ha a (by simp)) hn
    · exact ih (fun a hm => ha a (by simp [hm])) b hb

private theorem tiltAtoms_masks (vs : List Fraction) (normalizer : Fraction) (as : List PolicyAtom) :
    (tiltAtoms vs normalizer as).1.map Prod.snd = as.map Prod.snd := by
  induction as <;> simp [tiltAtoms, *]

theorem policyOutput_masks (vs ws : List Fraction) (D : Bits) (as : List BitAtom) :
    (policyOutput vs ws D as).1.map Prod.snd = as.map Prod.snd := by
  simp only [policyOutput,tiltAtoms_masks,liftAtoms_map,List.map_map]
  rfl

theorem policyOutput_valid_fractions (vs ws : List Fraction) (D : Bits) (as : List BitAtom)
    (hv : ∀ v ∈ vs,v.Valid) (hw : ∀ w ∈ ws,w.Valid) (hD : 0<value D) :
    ∀ a ∈ (policyOutput vs ws D as).1,a.1.Valid := by
  apply tiltAtoms_valid_all vs (normalizer ws).1 (liftAtoms D as).1 hv (normalizer_positive ws hw)
  intro a ha
  rw [liftAtoms_map] at ha
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
  exact hD

/-- Raw output denominators are positive and masks retain exactly one bit per
original product; no postprocessing or padding is assumed. -/
theorem finishPolicy_raw_shape {n : ℕ} (ks : Bits) (vs ws : List Fraction)
    (hvl : vs.length=n) (hwl : ws.length=n)
    (hv : ∀ v ∈ vs,v.Valid) (hw : ∀ w ∈ ws,w.Valid) (hvp : ∀ v ∈ vs,0<v.decode) :
    ∀ a ∈ (finishPolicy ks vs ws).1,a.1.Valid ∧ a.2.length=n := by
  let ms := (marginalBits ws vs).1
  let sparse := binaryGreedyRank ks (ms.map Fraction.numerator) (ms.map Fraction.denominator)
  have hm := marginalBits_valid ws vs hw hvp
  have hD : 0<value sparse.1 := by
    simpa only [sparse,binaryGreedyRank,binaryGreedy,rankTokens_length] using product_denominator_positive ms hm
  have hvalid := policyOutput_valid_fractions vs ws sparse.1 sparse.2.1 hv hw hD
  have hshape := sparse_binary_shape ks (ms.map Fraction.numerator) (ms.map Fraction.denominator) le_rfl
  have hml : ms.length=n := by simp [ms,hwl,hvl]
  intro a ha
  change a ∈ (policyOutput vs ws sparse.1 sparse.2.1).1 at ha
  refine ⟨hvalid a ha,?_⟩
  have hm : a.2 ∈ (policyOutput vs ws sparse.1 sparse.2.1).1.map Prod.snd := List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [policyOutput_masks] at hm
  obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
  have hh := (hshape.2.2 b hb).2
  rw [he] at hh
  simpa only [List.length_map,hml] using hh

theorem runPolicyBits_raw_shape {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : Bits) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i) :
    ∀ a ∈ (runPolicyBits alpha epsilon ks (sourceProducts rv)).1,a.1.Valid ∧ a.2.length=n+1 := by
  let capacity : Fraction := ⟨ks,[true]⟩
  have hc : capacity.Valid := by norm_num [capacity,Fraction.Valid,value]
  have hcd : capacity.decode=(d.K : ℚ) := by simp [capacity,Fraction.decode,value,hK]
  have hs := runSalesBits_semantics d hd ε hε alpha epsilon capacity rv ha he hc had hed hcd hprod hdec
  let vs := (sourceProducts rv).map Prod.snd
  let ws := (runSalesBits alpha epsilon capacity (sourceProducts rv)).1
  have hv : ∀ v ∈ vs,v.Valid := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact (hprod i).2
  have hvp : ∀ v ∈ vs,0<v.decode := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    rw [(hdec i).2]
    exact (hd.1 i).2
  exact finishPolicy_raw_shape ks vs ws (by simp [vs,sourceProducts]) hs.1 hv hs.2.1 hvp

end BalancedAssortments.FPTASCostComplete
