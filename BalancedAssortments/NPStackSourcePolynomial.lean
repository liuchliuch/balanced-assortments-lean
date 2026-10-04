import BalancedAssortments.NPStackSourceInitial
import BalancedAssortments.NPPolynomialPrograms

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexitySourceModel
open FPTASCostProgram (serializeBits)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def clockValue (L : ℕ) : ℕ := loopBudget L L+1000*(L+5)+fixedNoSource.length+100
noncomputable def sourceClock : Polynomial ℕ :=
  (Polynomial.X+1)*Polynomial.C loopConstant*(Polynomial.X+5)^2+
    1000*(Polynomial.X+5)+Polynomial.C (fixedNoSource.length+100)

lemma sourceClock_eval (L : ℕ) : sourceClock.eval L=clockValue L := by
  simp [sourceClock,clockValue,loopBudget]
  ring

lemma loopBudget_mono_remaining {L a b : ℕ} (h : a≤b) : loopBudget L a≤loopBudget L b := by
  unfold loopBudget
  gcongr

/-- The entire finite transducer computes the total language-reduction function
on every raw input string, with a genuine cubic transition clock. -/
theorem source_run (bits : List Bool) :
    ∃ t≤clockValue bits.length,∃ out,Run program t (initial program bits) out ∧
      accepts program out ∧ out.stk .wireOut=reductionSpec bits := by
  rw [initial_cfg]
  cases hp : (EncodingTime.parseField bits).1 with
  | none =>
    obtain ⟨t,ht,after,hr,hout⟩ := read_failure .readTarget .normalizeTarget
      (stable bits [] [] [] [] []) rfl rfl rfl rfl hp
    simp only [stable,store_wireIn,store_wireOut] at ht hout
    obtain ⟨out,hno,ha,hv⟩ := fixed_no_run after
    rw [hout] at hno
    simp only [List.length_nil,Nat.zero_add] at hno
    refine ⟨t+(1+fixedNoSource.length),?_,out,hr.trans hno,ha,?_⟩
    · unfold clockValue
      omega
    · rw [reductionSpec_bad bits hp]
      exact hv
  | some parsed =>
    rcases parsed with ⟨payload,rest⟩
    have hwire := NPStackField.parseField_sound bits payload rest hp
    have hlength : bits.length=2*payload.length+1+rest.length := by
      rw [hwire]
      simp [serializeBits]
      omega
    have hne : bits≠[] := by rw [hwire];simp [serializeBits]
    have hpw : payload.length≤bits.length := by omega
    have hbw : (value payload).bits.length≤bits.length := (canonical_width payload).trans hpw
    obtain ⟨tr,htr,hr⟩ := read_target_run payload rest
    rw [← hwire] at hr
    by_cases hpos : 0<value payload
    · have htest := positive_target_run rest (value payload).bits (bits_nonempty hpos)
      obtain ⟨ts,hts,hs⟩ := seeds_run rest [] (value payload).bits
      simp only [value_bits] at hs
      obtain ⟨tl,htl,out,hl,ha,hv⟩ := loop_run (value payload) [] rest bits.length hbw
        (by simp) (by simp only [List.length_nil,Nat.zero_add];omega)
      have hl' : Run program tl
          (cfg (.probe false) (stable rest [] (value payload).bits (3*value payload).bits (5*value payload).bits [true])) out := by
        simpa [bodyWire] using hl
      have hmono := loopBudget_mono_remaining (L := bits.length) (show rest.length≤bits.length by omega)
      refine ⟨tr+2+ts+tl,?_,out,((hr.trans htest).trans hs).trans hl',ha,?_⟩
      · unfold clockValue
        omega
      · rw [reductionSpec_field bits payload rest hne hp,if_pos hpos]
        exact hv
    · have hz : value payload=0 := by omega
      simp only [hz,Nat.zero_bits] at hr
      have htest := zero_target_run rest
      obtain ⟨out,hno,ha,hv⟩ := fixed_no_run (stable rest [] [] [] [] [])
      simp only [stable,store_wireOut,List.length_nil,Nat.zero_add] at hno
      refine ⟨tr+1+(1+fixedNoSource.length),?_,out,(hr.trans htest).trans hno,ha,?_⟩
      · unfold clockValue
        omega
      · rw [reductionSpec_field bits payload rest hne hp,if_neg hpos]
        exact hv

/-- This packages actual finite code, all-input computations and a polynomial
clock; it is not a semantic function with a freely attached cost counter. -/
noncomputable def polynomialReduction : PolynomialProgram reductionSpec where
  code := finiteProgram
  noChoice := program_noChoice
  clock := sourceClock
  computes bits := by
    rw [sourceClock_eval]
    exact source_run bits

/-- A genuine finite-machine-backed total many-one hardness link. -/
theorem positiveSubsetSum_reduces_source :
    PolyManyOne {bits | NPSATSubsetSum.PositiveSubsetSumLanguage bits}
      {bits | ComplexityTimeSourceParsing.SourceLanguage bits} := by
  refine ⟨reductionSpec,⟨polynomialReduction⟩,?_⟩
  intro bits
  exact (reductionSpec_correct bits).symm

end BalancedAssortments.NPStackSourceReduction
