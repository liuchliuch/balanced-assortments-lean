import BalancedAssortments.FPTASCostCodec

namespace BalancedAssortments.FPTASCostCodec
open KnapsackCostRational FPTASCostSeeds FPTASCostOutput

lemma parseProducts_sound (fs : List (List Bool)) (ps : List Product)
    (h : (parseProducts fs).1 = some ps) : productFields ps = fs := by
  fun_induction parseProducts fs generalizing ps
  · simp_all [productFields]
  · rename_i a b c d xs tail ih
    subst tail
    cases ht : (parseProducts xs).1 with
    | none => simp [ht] at h
    | some qs =>
      simp only [ht,Option.map_some,Option.some.injEq] at h
      subst ps
      simpa only [productFields] using congrArg (fun fs => a::b::c::d::fs) (ih qs ht)
  · simp_all

lemma pack_sound (fs : List (List Bool)) (x : Input)
    (h : (pack fs).1 = some x) : fields x = fs := by
  unfold pack at h
  split at h
  · rename_i a b c d k rest
    cases ht : (parseProducts rest).1 with
    | none => simp [ht] at h
    | some ps =>
      simp only [ht,Option.map_some,Option.some.injEq] at h
      subst x
      simpa only [fields] using congrArg (fun fs => a::b::c::d::k::fs) (parseProducts_sound rest ps ht)
  · simp_all

/-- Successful framing bounds every original stored bit, without canonicalization. -/
theorem parse_volume (bs : List Bool) (x : Input) (h : (parse bs).1 = some x) :
    NPCNF.Encoding.fieldVolume (fields x) ≤ bs.length := by
  unfold parse at h
  cases hr : (EncodingTime.parse bs).1 with
  | none => simp [hr] at h
  | some fs =>
    have hp : (pack fs).1 = some x := by simpa [hr] using h
    rw [pack_sound fs x hp]
    exact ComplexityTimeSourceParsing.parse_volume bs fs hr

theorem parse_inputSize (bs : List Bool) (x : Input) (h : (parse bs).1 = some x) :
    FPTASCostProgram.inputSize x.alpha x.epsilon (⟨x.rank,[true]⟩ : Fraction) x.products ≤ bs.length := by
  have hh := parse_volume bs x h
  rw [fields_volume] at hh
  dsimp only [FPTASCostProgram.inputSize,FPTASCostProgram.fractionSize] at *
  simp only [List.length_cons,List.length_nil] at *
  omega

end BalancedAssortments.FPTASCostCodec
