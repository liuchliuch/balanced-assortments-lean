import BalancedAssortments.FixedSupportCostProgram
import BalancedAssortments.FixedSupportCostEvaluateCorrect
import BalancedAssortments.FixedSupportCostScaleCoverage
import BalancedAssortments.FixedSupportCostPointSet
import BalancedAssortments.FixedSupportAlgorithmCorrect

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints
open FixedSupportCostOrder FixedSupportCostScaleList FixedSupportCostEvaluate FixedSupportCostMax
open FixedSupportAlgorithm

/-- Exact interpretation of a cached labeled output; this is a relation, not a
runtime decoding or rational normalization step. -/
def Realizes {n : ℕ} (r v : Fin n→ℚ) (α K : ℚ) (out : Result (Fin n)) (p : ℚ×ℚ) : Prop :=
  out.1.map (fun x => (x.1,decode x.2)) =
    (scoreOrder r v p.1).map (fun i => (i,candidateVector r v α K p i)) ∧
  decode out.2=fractionalRevenue r (candidateVector r v α K p)

theorem raw_scores_canonical {n : ℕ} (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (hlabels : ps.map Prod.fst=List.finRange n) (hp : ∀ p ∈ ps,p.2.Valid)
    (hv : ∀ i,v i≠0) (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1) :
    ((scorePoints (ps.map Prod.snd)).1.map decode).toFinset=scoreSamples r v := by
  have hvalid : ∀ p ∈ ps.map Prod.snd,p.Valid := by
    intro p hm
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    exact hp q hq
  rw [scorePoints_decode _ hvalid]
  have hd : (ps.map Prod.snd).map decodeProduct=List.ofFn (fun i => (r i,v i)) := by
    rw [List.ofFn_eq_map,← hlabels]
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro p hm
    exact Prod.ext (hdata p hm).1 (hdata p hm).2
  rw [hd,scoreValues_toFinset r v hv]

theorem candidates_valid {I : Type*} (α K : Fraction) (ps : List (I×Product))
    (hp : ∀ p ∈ ps,p.2.Valid) (hα : Valid α) (hK : Valid K) :
    ∀ out ∈ (candidates α K ps).1,(∀ x ∈ out.1,Valid x.2) ∧ Valid out.2 := by
  have hp' : ∀ p ∈ ps.map Prod.snd,p.Valid := by
    intro p hm;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm;exact hp q hq
  intro out hout
  obtain ⟨ρ,hρ,hh⟩ := (candidates_member α K ps out).mp hout
  obtain ⟨t,ht,rfl⟩ := (pattern_member α K ps ρ out).mp hh
  have hρv := scorePoints_valid _ hp' ρ hρ
  have hrows := ordered_valid ps ρ hp hρv
  have hvs : ∀ v ∈ (ordered ps ρ).1.map (fun r => r.product.2),Valid v := by
    intro v hm;obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hm;exact (hrows s hs).1.2
  exact evaluateOrdered_valid _ _ _ _ hα hK (scalePoints_valid _ _ _ hα hK hvs t ht) hrows

theorem candidates_sound {n : ℕ} (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (α K : Fraction) (hlabels : ps.map Prod.fst=List.finRange n)
    (hp : ∀ p ∈ ps,p.2.Valid) (hv : ∀ i,v i≠0) (hα : Valid α) (hK : Valid K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1)
    {out : Result (Fin n)} (hout : out ∈ (candidates α K ps).1) :
    ∃ p ∈ FixedSupportAlgorithm.candidates r v (decode α) (decode K),
      Realizes r v (decode α) (decode K) out p := by
  obtain ⟨ρ,hρ,hts⟩ := (candidates_member α K ps out).mp hout
  obtain ⟨t,ht,rfl⟩ := (pattern_member α K ps ρ out).mp hts
  have hp' : ∀ p ∈ ps.map Prod.snd,p.Valid := by
    intro p hm;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm;exact hp q hq
  have hρv := scorePoints_valid _ hp' ρ hρ
  have hrows := ordered_valid ps ρ hp hρv
  have hvs : ∀ v ∈ (ordered ps ρ).1.map (fun s => s.product.2),Valid v := by
    intro v hm;obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hm;exact (hrows s hs).1.2
  have htv := scalePoints_valid _ _ _ hα hK hvs t ht
  refine ⟨(decode ρ,decode t),(mem_candidates r v _ _ _).mpr ⟨?_,?_⟩,?_⟩
  · rw [← raw_scores_canonical r v ps hlabels hp hv hdata]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ρ,hρ,rfl⟩)
  · rw [← ordered_scalePoints_canonical r v ps ρ α K hlabels hp hρv hα hK hdata]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩)
  · exact evaluate_ordered_candidate r v ps ρ α K t hlabels hp hρv hα hK htv hdata

theorem candidates_complete {n : ℕ} (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (α K : Fraction) (hlabels : ps.map Prod.fst=List.finRange n)
    (hp : ∀ p ∈ ps,p.2.Valid) (hv : ∀ i,v i≠0) (hα : Valid α) (hK : Valid K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1)
    {p : ℚ×ℚ} (hpm : p ∈ FixedSupportAlgorithm.candidates r v (decode α) (decode K)) :
    ∃ out ∈ (candidates α K ps).1,Realizes r v (decode α) (decode K) out p := by
  have hm := (mem_candidates r v _ _ p).mp hpm
  rw [← raw_scores_canonical r v ps hlabels hp hv hdata] at hm
  obtain ⟨ρ,hρ,heρ⟩ := List.mem_map.mp (List.mem_toFinset.mp hm.1)
  have hp' : ∀ p ∈ ps.map Prod.snd,p.Valid := by
    intro p hm;obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm;exact hp q hq
  have hρv := scorePoints_valid _ hp' ρ hρ
  have htm : p.2 ∈ scaleSamples r v (decode α) (decode K) (decode ρ) := by simpa only [heρ] using hm.2
  rw [← ordered_scalePoints_canonical r v ps ρ α K hlabels hp hρv hα hK hdata] at htm
  obtain ⟨t,ht,het⟩ := List.mem_map.mp (List.mem_toFinset.mp htm)
  have hrows := ordered_valid ps ρ hp hρv
  have hvs : ∀ v ∈ (ordered ps ρ).1.map (fun s => s.product.2),Valid v := by
    intro v hm;obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hm;exact (hrows s hs).1.2
  have htv := scalePoints_valid _ _ _ hα hK hvs t ht
  refine ⟨(evaluateOrdered α K t (ordered ps ρ).1).1,?_,?_⟩
  · exact (candidates_member _ _ _ _).mpr ⟨ρ,hρ,(pattern_member _ _ _ _ _).mpr ⟨t,ht,rfl⟩⟩
  · have hh := evaluate_ordered_candidate r v ps ρ α K t hlabels hp hρv hα hK htv hdata
    simpa only [Realizes,heρ,het,Prod.mk.eta] using hh

/-- The actual binary search returns a source candidate with exactly the
optimal value of the independently certified rational search. -/
theorem runBits_refines {n : ℕ} (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (α K : Fraction) (hlabels : ps.map Prod.fst=List.finRange n)
    (hp : ∀ p ∈ ps,p.2.Valid) (hv : ∀ i,v i≠0) (hα : Valid α) (hK : Valid K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1) :
    ∃ out p, (runBits α K ps).1=some out ∧
      p ∈ FixedSupportAlgorithm.candidates r v (decode α) (decode K) ∧
      Realizes r v (decode α) (decode K) out p ∧
      (∀ x ∈ out.1,Valid x.2) ∧ Valid out.2 ∧
      decode out.2=fractionalRevenue r (optimize r v (decode α) (decode K)) := by
  obtain ⟨initial,hinitial,_⟩ := candidates_complete r v ps α K hlabels hp hv hα hK hdata
    (zero_mem_candidates r v (decode α) (decode K))
  have hne : (candidates α K ps).1≠[] := by intro he;simpa [he] using hinitial
  have hsome : (runBits α K ps).1≠none := (best_some_iff _).mpr hne
  cases he : (runBits α K ps).1 with
  | none => exact (hsome he).elim
  | some out =>
    have hom := runBits_member α K ps he
    obtain ⟨p,hpm,hreal⟩ := candidates_sound r v ps α K hlabels hp hv hα hK hdata hom
    have hvalid := candidates_valid α K ps hp hα hK
    obtain ⟨best,hbm,hbr⟩ := candidates_complete r v ps α K hlabels hp hv hα hK hdata
      (bestCandidate_mem r v (decode α) (decode K))
    have hlo := runBits_dominates α K ps (fun x hx => (hvalid x hx).2) he best hbm
    rw [hbr.2] at hlo
    have hhi := optimize_dominates_candidates r v (decode α) (decode K) hpm
    refine ⟨out,p,rfl,hpm,hreal,(hvalid out hom).1,(hvalid out hom).2,?_⟩
    apply le_antisymm
    · rw [hreal.2]
      exact hhi
    · exact hlo

/-- Raw binary prescribed-support solver: a finite labeled output, positive
raw denominators, source feasibility, and optimality against every real point. -/
theorem runBits_optimal {n : ℕ} (hn : 0<n) (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (α K : Fraction) (hlabels : ps.map Prod.fst=List.finRange n)
    (hp : ∀ p ∈ ps,p.2.Valid) (hr : ∀ i,0<r i) (hv : ∀ i,0<v i)
    (hα : Valid α) (hK : Valid K) (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1) :
    ∃ out p, (runBits α K ps).1=some out ∧
      Realizes r v (decode α) (decode K) out p ∧
      (∀ x ∈ out.1,Valid x.2) ∧ Valid out.2 ∧
      FixedSupportReal.Feasible (fun i => (v i : ℝ)) (decode α : ℝ) (decode K : ℝ)
        (fun i => (candidateVector r v (decode α) (decode K) p i : ℝ)) ∧
      (∀ w : Fin n→ℝ,FixedSupportReal.Feasible (fun i => (v i : ℝ))
        (decode α : ℝ) (decode K : ℝ) w →
        FixedSupportReal.revenue (fun i => (r i : ℝ)) w≤(decode out.2 : ℝ)) := by
  obtain ⟨out,p,he,hpm,hreal,hvalid,hov,hvalue⟩ := runBits_refines r v ps α K hlabels hp
    (fun i => ne_of_gt (hv i)) hα hK hdata
  have hm := (mem_candidates r v _ _ p).mp hpm
  have ht := scaleSamples_bounds r v (decode α) (decode K) p.1
    (scaleUpper_pos hn v hv hKpos).le hm.2
  have hf := candidateVector_feasible r v hv hαpos hα1 hKpos.le ht.1 ht.2 (ρ := p.1)
  refine ⟨out,p,he,hreal,hvalid,hov,?_,?_⟩
  · simpa only [Prod.mk.eta] using hf
  · intro w hw
    rw [hvalue]
    exact optimize_optimal hn r v hr hv hαpos hα1 hKpos w hw

theorem optimal_candidate_positive {n : ℕ} (hn : 0<n) (r v : Fin n→ℚ)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<v i) {α K : ℚ}
    (hα : 0<α) (hα1 : α≤1) (hK : 0<K) (p : ℚ×ℚ)
    (hf : FixedSupportReal.Feasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ)
      (fun i => (candidateVector r v α K p i : ℝ)))
    (he : fractionalRevenue r (candidateVector r v α K p)=fractionalRevenue r (optimize r v α K)) :
    ∀ i,0<candidateVector r v α K p i := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hp := optimize_exact_support hn r v hr hv hα hα1 hK
  have hnum : 0<∑ i,r i*optimize r v α K i :=
    Finset.sum_pos (fun i _ => mul_pos (hr i) (hp i)) Finset.univ_nonempty
  have hsum : 0≤∑ i,optimize r v α K i := Finset.sum_nonneg (fun i _ => (hp i).le)
  have hrev : 0<fractionalRevenue r (optimize r v α K) := div_pos hnum (by linarith)
  have hrev' : (0 : ℝ)<FixedSupportReal.revenue (fun i => (r i : ℝ))
      (fun i => (candidateVector r v α K p i : ℝ)) := by
    rw [realRevenue_cast,he]
    exact_mod_cast hrev
  have hnum' := (div_pos_iff_of_pos_right
    (FixedSupportReal.denominator_pos _ (fun i => (hf.1 i).1))).mp hrev'
  have hαR : (0 : ℝ)<(α : ℝ) := by exact_mod_cast hα
  have hh := FixedSupportReal.positive_objective_exact_support
    (fun i => (r i : ℝ)) (fun i => (candidateVector r v α K p i : ℝ)) (α : ℝ)
    hαR (fun i => (hf.1 i).1) hf.2.2 hnum'
  intro i
  have hi := hh i
  dsimp only at hi
  exact_mod_cast hi

theorem runBits_exact_support {n : ℕ} (hn : 0<n) (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (α K : Fraction) (hlabels : ps.map Prod.fst=List.finRange n)
    (hp : ∀ p ∈ ps,p.2.Valid) (hr : ∀ i,0<r i) (hv : ∀ i,0<v i)
    (hα : Valid α) (hK : Valid K) (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1) :
    ∃ out p, (runBits α K ps).1=some out ∧
      Realizes r v (decode α) (decode K) out p ∧
      (∀ x ∈ out.1,Valid x.2) ∧ Valid out.2 ∧
      (∀ i,0<candidateVector r v (decode α) (decode K) p i) ∧
      FixedSupportReal.Feasible (fun i => (v i : ℝ)) (decode α : ℝ) (decode K : ℝ)
        (fun i => (candidateVector r v (decode α) (decode K) p i : ℝ)) ∧
      (∀ w : Fin n→ℝ,FixedSupportReal.Feasible (fun i => (v i : ℝ))
        (decode α : ℝ) (decode K : ℝ) w →
        FixedSupportReal.revenue (fun i => (r i : ℝ)) w≤(decode out.2 : ℝ)) := by
  obtain ⟨out,p,he,hreal,hvalid,hov,hf,hopt⟩ := runBits_optimal hn r v ps α K hlabels hp hr hv
    hα hK hαpos hα1 hKpos hdata
  have hbest := optimize_feasible hn r v hv hαpos hα1 hKpos
  have hlo := hopt _ hbest
  rw [realRevenue_cast,hreal.2] at hlo
  have hhi := optimize_optimal hn r v hr hv hαpos hα1 hKpos _ hf
  rw [realRevenue_cast] at hhi
  have hval : fractionalRevenue r (candidateVector r v (decode α) (decode K) p)=
      fractionalRevenue r (optimize r v (decode α) (decode K)) := by
    have hh := le_antisymm hhi hlo
    exact_mod_cast hh
  exact ⟨out,p,he,hreal,hvalid,hov,
    optimal_candidate_positive hn r v hr hv hαpos hα1 hKpos p hf hval,hf,hopt⟩

end BalancedAssortments.FixedSupportCostProgram
