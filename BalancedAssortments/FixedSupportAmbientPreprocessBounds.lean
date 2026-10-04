import BalancedAssortments.FixedSupportAmbientPreprocess

namespace BalancedAssortments.FixedSupportAmbientPreprocess
open FixedSupportCostPoints FixedSupportCostProgram FixedSupportCostRational
open ComplexityTimeFractions (Valid)

def productVolume (p : Product) : ℕ := fractionVolume p.1+fractionVolume p.2
def ambientVolume (α K : Fraction) (ps : List Product) (mask : List Bool) : ℕ :=
  1+ps.length+mask.length+fractionVolume α+fractionVolume K+(ps.map productVolume).sum

lemma sublist_volume {ps qs : List Product} (h : ps.Sublist qs) :
    (ps.map productVolume).sum ≤ (qs.map productVolume).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons,List.sum_cons];omega
  | cons₂ a h ih => simp only [List.map_cons,List.sum_cons];omega

lemma prepared_inputVolume {ps : List Product} {mask : List Bool} {out : Prepared}
    (h : (prepare ps mask).1=some out) (α K : Fraction) :
    inputVolume α K out.indexed ≤ ambientVolume α K ps mask := by
  have hc := prepare_correct h
  have hlen : out.indexed.length=out.products.length := by
    have hh := congrArg List.length hc.2.2.2.2.2
    simpa only [List.length_map] using hh
  have hpay : (out.indexed.map (fun p => fractionVolume p.2.1+fractionVolume p.2.2)).sum=
      (out.products.map productVolume).sum := by
    simpa only [List.map_map,Function.comp_def,productVolume] using
      congrArg (fun xs : List Product => (xs.map productVolume).sum) hc.2.2.2.2.2
  have hs := sublist_volume hc.2.2.1
  have hn := hc.2.2.1.length_le
  unfold inputVolume ambientVolume
  rw [hlen,hpay]
  omega

lemma prepared_valid {ps : List Product} {mask : List Bool} {out : Prepared}
    (h : (prepare ps mask).1=some out) (hp : ∀ p∈ps,p.Valid) :
    ∀ p∈out.indexed,p.2.Valid := by
  intro p hm
  have hc := prepare_correct h
  have hmem : p.2∈out.products := by
    have hm' : p.2∈out.indexed.map Prod.snd := List.mem_map.mpr ⟨p,hm,rfl⟩
    simpa only [hc.2.2.2.2.2] using hm'
  exact hp _ (hc.2.2.1.subset hmem)

lemma ambient_count_le (α K : Fraction) (ps : List Product) (mask : List Bool) :
    ps.length ≤ ambientVolume α K ps mask := by unfold ambientVolume;omega

/-- Selection, shape rejection, positional reindexing, and the exact raw
solver share a single polynomial bound in the full ambient input plus mask.
No selected-subinstance width or length bound is supplied by the caller. -/
theorem prepared_solver_polynomial : ∃ P : Polynomial ℕ,∀ (α K : Fraction)
    (ps : List Product) (mask : List Bool) (out : Prepared),
    Valid α → Valid K → (∀ p∈ps,p.Valid) → (prepare ps mask).1=some out →
    (prepare ps mask).2+(runBits α K out.indexed).2+3 ≤ P.eval (ambientVolume α K ps mask) := by
  obtain ⟨Q,hQ⟩ := runCost_polynomial
  refine ⟨Q+(4*Polynomial.X+1+(Polynomial.X+1)*(Polynomial.X+6)+6),?_⟩
  intro α K ps mask out ha hk hp hout
  let I := ambientVolume α K ps mask
  have hinput : inputVolume α K out.indexed ≤ I := prepared_inputVolume hout α K
  have hn := (inputVolume_bounds α K out.indexed).1.trans hinput
  have hcost := runBits_input_cost α K out.indexed ha hk (prepared_valid hout hp)
  have hbackend : (runBits α K out.indexed).2 ≤ runCost I I :=
    hcost.trans ((runCost_mono_count hn).trans (runCost_mono_width hinput))
  have hn' : ps.length ≤ I := ambient_count_le α K ps mask
  have hprep := prepare_cost ps mask
  have hprod : (ps.length+1)*(ps.length+6) ≤ (I+1)*(I+6) := by gcongr
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  rw [← hQ]
  change _ ≤ runCost I I+(4*I+1+(I+1)*(I+6)+6)
  omega

end BalancedAssortments.FixedSupportAmbientPreprocess
