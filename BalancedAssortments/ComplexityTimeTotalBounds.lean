import BalancedAssortments.ComplexityTimeTotalVerifier
import BalancedAssortments.ComplexityTimeParsingBounds

namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline

lemma pair_size_sum (xs : List (Fraction × Fraction)) :
    ((xs.map Prod.snd).map fractionSize).sum+((xs.map Prod.fst).map fractionSize).sum =
      (xs.map (fun rv => fractionSize rv.1+fractionSize rv.2)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; omega

lemma sourceInputSize_le_measure (s : Source) :
    sourceInputSize s.attractions s.prices s.alpha s.target s.capacity ≤ sourceMeasure s := by
  have h := pair_size_sum s.products
  simp only [sourceInputSize,Source.attractions,Source.prices,List.length_map,
    sourceMeasure,productsMeasure]
  omega

lemma totalInputSize_le_measure (s : Source) (c : Certificate) :
    totalInputSize s.attractions s.prices s.alpha s.target s.capacity c.mask c.numerators c.denominator ≤
      sourceMeasure s+certificateMeasure c := by
  have h := pair_size_sum s.products
  simp only [totalInputSize,Source.attractions,Source.prices,List.length_map,
    sourceMeasure,productsMeasure,certificateMeasure,tripleMeasure]
  omega

noncomputable def totalTimePolynomial : Polynomial ℕ :=
  sourceTimePolynomial+2400*(Polynomial.X+1)^2

lemma totalTimePolynomial_eval (L : ℕ) :
    totalTimePolynomial.eval L = sourceTimePolynomial.eval L+2400*(L+1)^2 := by
  simp [totalTimePolynomial]

set_option maxRecDepth 4096 in
lemma verifyParsed_cost (s : Source) (c : Certificate) :
    (verifyParsed s c).2 ≤ sourceTimePolynomial.eval (sourceMeasure s+certificateMeasure c)+
      2000*(sourceMeasure s+certificateMeasure c+1)^2 := by
  have hs := validateSource_cost s
  have hc := validateCertificate_cost s c
  have hn := (source_widths s).1
  have hsq := Nat.mul_self_le_mul_self (show sourceMeasure s+1 ≤ sourceMeasure s+certificateMeasure c+1 by omega)
  unfold verifyParsed
  dsimp only
  split_ifs with guard
  · have hg : (validateSource s).1 = true ∧ (validateCertificate s c).1 = true := by
      simpa only [Bool.and_eq_true] using guard
    have hv := (validateCertificate_correct s c).mp hg.2
    have hraw := verifySource_polynomial_cost s.attractions s.prices s.alpha s.target s.capacity
      c.mask c.numerators c.denominator (by simp [Source.prices,Source.attractions])
      (by simp only [Source.attractions,List.length_map]; omega)
    have hm := sourceTimePolynomial_mono (totalInputSize_le_measure s c)
    nlinarith only [hs,hc,hn,hsq,hraw,hm]
  · nlinarith only [hs,hc,hn,hsq]

/-- Unconditional cost bound, including malformed inputs, all parsing and all
legality checks, in the actual two serialized bitstring lengths. -/
theorem totalVerify_polynomial_cost (sourceBits certificateBits : List Bool) :
    (totalVerify sourceBits certificateBits).2 ≤
      totalTimePolynomial.eval (sourceBits.length+certificateBits.length) := by
  have hs := parseSource_cost sourceBits
  have hc := parseCertificate_cost certificateBits
  let L := sourceBits.length+certificateBits.length
  have hsL := Nat.mul_self_le_mul_self (show sourceBits.length+1 ≤ L+1 by dsimp [L]; omega)
  have hcL := Nat.mul_self_le_mul_self (show certificateBits.length+1 ≤ L+1 by dsimp [L]; omega)
  rw [totalTimePolynomial_eval]
  change _ ≤ sourceTimePolynomial.eval L+2400*(L+1)^2
  unfold totalVerify
  dsimp only
  cases hsp : (parseSource sourceBits).1 with
  | none => simp only [hsp]; nlinarith
  | some s =>
    cases hcp : (parseCertificate certificateBits).1 with
    | none => simp only [hsp,hcp]; nlinarith
    | some c =>
      have sm := parseSource_measure sourceBits s hsp
      have cm := parseCertificate_measure certificateBits c hcp
      have hm : sourceMeasure s+certificateMeasure c ≤ L := by dsimp [L]; omega
      have hp := sourceTimePolynomial_mono hm
      have hsq := Nat.mul_self_le_mul_self (Nat.add_le_add_right hm 1)
      have hv := verifyParsed_cost s c
      simp only [hsp,hcp]
      nlinarith

end BalancedAssortments.ComplexityTimeSourceParsing
