import BalancedAssortments.FixedSupportAmbientPreprocessBounds

/-! Actual ambient-input exact-support wrapper. Unequal lengths and empty
selected support are explicit errors; the nonempty source case invokes the
already certified raw solver on the physically selected positional records. -/
namespace BalancedAssortments.FixedSupportAmbientPreprocess
open FixedSupportCostPoints FixedSupportCostProgram FixedSupportCostRational
open ComplexityTimeFractions (Valid)

abbrev AmbientResult := (out : Prepared) × FixedSupportCostMax.Result (Fin out.products.length)

def runAmbient (α K : Fraction) (ps : List Product) (mask : List Bool) : Option AmbientResult × ℕ :=
  let prep := prepare ps mask
  match prep.1 with
  | none => (none,prep.2+1)
  | some out =>
    if out.products.isEmpty then (none,prep.2+1) else
      let ans := runBits α K out.indexed
      (ans.1.map (fun result => (⟨out,result⟩ : AmbientResult)),prep.2+ans.2+3)

theorem runAmbient_returns (α K : Fraction) (ps : List Product) (mask : List Bool)
    (out : Prepared) (result : FixedSupportCostMax.Result (Fin out.products.length))
    (hp : (prepare ps mask).1=some out) (hne : out.products≠[])
    (hr : (runBits α K out.indexed).1=some result) :
    (runAmbient α K ps mask).1=some ⟨out,result⟩ := by
  simp [runAmbient,hp,List.isEmpty_iff,hne,hr]

theorem runAmbient_some {α K : Fraction} {ps : List Product} {mask : List Bool} {result : AmbientResult}
    (h : (runAmbient α K ps mask).1=some result) :
    (prepare ps mask).1=some result.1 ∧ result.1.products≠[] ∧
      (runBits α K result.1.indexed).1=some result.2 := by
  unfold runAmbient at h
  cases hp : (prepare ps mask).1 with
  | none => simp [hp] at h
  | some out =>
    simp only [hp] at h
    by_cases he : out.products.isEmpty=true
    · simp [he] at h
    · rw [if_neg he] at h
      cases hr : (runBits α K out.indexed).1 with
      | none => simp only [hr,Option.map_none] at h;cases h
      | some r =>
        simp only [hr,Option.map_some,Option.some.injEq] at h
        cases h
        exact ⟨rfl,by simpa using he,hr⟩


@[simp] theorem runAmbient_empty (α K : Fraction) : runAmbient α K [] []=(none,7) := by
  simp [runAmbient]
theorem runAmbient_all_false (α K : Fraction) (ps : List Product) :
    (runAmbient α K ps (List.replicate ps.length false)).1=none := by
  obtain ⟨out,hp,he⟩ := prepare_all_false ps
  simp [runAmbient,hp,he]
theorem runAmbient_mismatch (α K : Fraction) (ps : List Product) (mask : List Bool)
    (h : ps.length≠mask.length) : (runAmbient α K ps mask).1=none := by
  simp [runAmbient,prepare_mismatch ps mask h]

/-- Total ambient program, including error paths and selection/reindexing, has
one polynomial counter bound in the original raw product fields plus mask. -/
theorem runAmbient_polynomial : ∃ P : Polynomial ℕ,∀ (α K : Fraction)
    (ps : List Product) (mask : List Bool),
    Valid α → Valid K → (∀ p∈ps,p.Valid) →
      (runAmbient α K ps mask).2 ≤ P.eval (ambientVolume α K ps mask) := by
  obtain ⟨Q,hQ⟩ := runCost_polynomial
  refine ⟨Q+(4*Polynomial.X+1+(Polynomial.X+1)*(Polynomial.X+6)+6),?_⟩
  intro α K ps mask ha hk hps
  let I := ambientVolume α K ps mask
  have hn : ps.length≤I := ambient_count_le α K ps mask
  have hp := prepare_cost ps mask
  have hp' : (prepare ps mask).2 ≤ 4*I+1+(I+1)*(I+6)+3 := by
    have hh : (ps.length+1)*(ps.length+6)≤(I+1)*(I+6) := by gcongr
    omega
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  rw [← hQ]
  change _ ≤ runCost I I+(4*I+1+(I+1)*(I+6)+6)
  unfold runAmbient
  cases he : (prepare ps mask).1 with
  | none => simp only [he];omega
  | some out =>
    simp only [he]
    split_ifs with hempty
    · simp only;omega
    · have hinput : inputVolume α K out.indexed≤I := prepared_inputVolume he α K
      have hn' := (inputVolume_bounds α K out.indexed).1.trans hinput
      have hc := runBits_input_cost α K out.indexed ha hk (prepared_valid he hps)
      have hc' : (runBits α K out.indexed).2≤runCost I I :=
        hc.trans ((runCost_mono_count hn').trans (runCost_mono_width hinput))
      simp only
      omega

end BalancedAssortments.FixedSupportAmbientPreprocess
