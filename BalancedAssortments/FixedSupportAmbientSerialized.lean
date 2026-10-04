import BalancedAssortments.FixedSupportAmbientProgram

namespace BalancedAssortments.FixedSupportAmbientPreprocess
open FixedSupportCostPoints FixedSupportCostProgram FixedSupportCostRational NPCNF
open ComplexityTimeFractions (Valid)

def ambientFields (α K : Fraction) (ps : List Product) (mask : List Bool) : List (List Bool) :=
  mask::inputFields α K (ps.map (fun p => ((),p)))
def serializedAmbient (α K : Fraction) (ps : List Product) (mask : List Bool) : List Bool :=
  Encoding.encodeFields (ambientFields α K ps mask)

lemma serializedAmbient_length (α K : Fraction) (ps : List Product) (mask : List Bool) :
    (serializedAmbient α K ps mask).length=
      2*mask.length+1+(serializedInput α K (ps.map (fun p => ((),p)))).length := by
  simp [serializedAmbient,ambientFields,Encoding.encodeFields,Encoding.encodePayload_length,serializedInput]

lemma ambientVolume_le_serialized (α K : Fraction) (ps : List Product) (mask : List Bool) :
    ambientVolume α K ps mask ≤ (serializedAmbient α K ps mask).length := by
  rw [serializedAmbient_length,serializedInput_length]
  simp only [List.length_map,List.map_map,Function.comp_def]
  unfold ambientVolume productVolume
  omega

theorem serializedAmbient_parses (α K : Fraction) (ps : List Product) (mask : List Bool) :
    (EncodingTime.parse (serializedAmbient α K ps mask)).1=some (ambientFields α K ps mask) :=
  Encoding.parseFields_encode _

private lemma polynomial_monotone (p : Polynomial ℕ) {a b : ℕ} (h : a≤b) : p.eval a≤p.eval b := by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- The whole ambient-mask preprocessing and optimization path is polynomial
in the original concrete self-delimiting input length, not the selected data's
length. This is the structured raw-program cost; flat parsing is not executed
by runAmbient itself and is not silently claimed here. -/
theorem runAmbient_polynomial_serialized : ∃ P : Polynomial ℕ,∀ (α K : Fraction)
    (ps : List Product) (mask : List Bool),Valid α → Valid K → (∀ p∈ps,p.Valid) →
      (runAmbient α K ps mask).2 ≤ P.eval (serializedAmbient α K ps mask).length := by
  obtain ⟨P,hP⟩ := runAmbient_polynomial
  exact ⟨P,fun α K ps mask ha hk hp => (hP α K ps mask ha hk hp).trans
    (polynomial_monotone P (ambientVolume_le_serialized α K ps mask))⟩

end BalancedAssortments.FixedSupportAmbientPreprocess
