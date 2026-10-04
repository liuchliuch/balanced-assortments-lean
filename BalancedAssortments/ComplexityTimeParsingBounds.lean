import BalancedAssortments.ComplexityTimeSourceValidation

namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline

def productsMeasure (xs : List (Fraction × Fraction)) : ℕ :=
  2*xs.length+(xs.map (fun rv => fractionSize rv.1+fractionSize rv.2)).sum

def sourceMeasure (s : Source) : ℕ :=
  productsMeasure s.products+fractionSize s.alpha+fractionSize s.target+
    s.capacity.length+s.declaredCount.length+1

def tripleMeasure (ms : List Bool) (ps : List ZBits) : ℕ :=
  ms.length+ps.length+(ps.map integerSize).sum

def certificateMeasure (c : Certificate) : ℕ := tripleMeasure c.mask c.numerators+integerSize c.denominator

theorem parseProducts_measure (fields : List (List Bool)) (xs : List (Fraction × Fraction))
    (h : (parseProducts fields).1 = some xs) : productsMeasure xs ≤ fieldVolume fields := by
  fun_induction parseProducts fields generalizing xs
  · simp at h
    subst xs
    simp [productsMeasure]
  · rename_i rp rn rd vp vn vd rest result ih
    subst result
    cases hr : (parseProducts rest).1 with
    | none => simp [hr] at h
    | some tail =>
      simp [hr] at h
      subst xs
      have ht := ih tail hr
      simp only [productsMeasure,List.length_cons,List.map_cons,List.sum_cons,
        fractionSize,fieldVolume_cons] at *
      omega
  · simp at h

theorem packSource_measure (fields : List (List Bool)) (s : Source)
    (h : (packSource fields).1 = some s) : sourceMeasure s ≤ fieldVolume fields := by
  fun_cases packSource fields
  · rename_i count K ap an ad hp hn hd rest result
    subst result
    cases hr : (parseProducts rest).1 with
    | none => simp [packSource,hr] at h
    | some products =>
      simp [packSource,hr] at h
      subst s
      have ht := parseProducts_measure rest products hr
      simp only [sourceMeasure,fractionSize,fieldVolume_cons]
      omega
  · simp_all [packSource]

theorem parseSource_measure (bits : List Bool) (s : Source)
    (h : (parseSource bits).1 = some s) : sourceMeasure s ≤ bits.length := by
  unfold parseSource at h
  cases hp : (EncodingTime.parse bits).1 with
  | none => simp [hp] at h
  | some fields =>
    have hs : (packSource fields).1 = some s := by simpa [hp] using h
    exact (packSource_measure fields s hs).trans (parse_volume bits fields hp)

theorem parseTriples_measure (fields : List (List Bool)) (ms : List Bool) (ps : List ZBits)
    (h : (parseTriples fields).1 = some (ms,ps)) : tripleMeasure ms ps ≤ fieldVolume fields := by
  fun_induction parseTriples fields generalizing ms ps
  · simp at h
    rcases h with ⟨rfl,rfl⟩
    simp [tripleMeasure]
  · rename_i mb pp pn rest m r ih
    subst m
    subst r
    cases hm : (parseMask mb).1 with
    | none => simp [hm] at h
    | some b =>
      cases hr : (parseTriples rest).1 with
      | none => simp [hm,hr] at h
      | some pair =>
        obtain ⟨ms',ps'⟩ := pair
        simp [hm,hr] at h
        rcases h with ⟨rfl,rfl⟩
        have hh := ih ms' ps' hr
        simp only [tripleMeasure,List.length_cons,List.map_cons,List.sum_cons,integerSize,fieldVolume_cons] at *
        omega
  · simp at h

theorem packCertificate_measure (fields : List (List Bool)) (c : Certificate)
    (h : (packCertificate fields).1 = some c) : certificateMeasure c ≤ fieldVolume fields := by
  fun_cases packCertificate fields
  · rename_i qp qn rest r
    subst r
    cases hr : (parseTriples rest).1 with
    | none => simp [packCertificate,hr] at h
    | some pair =>
      obtain ⟨ms,ps⟩ := pair
      simp [packCertificate,hr] at h
      subst c
      have hh := parseTriples_measure rest ms ps hr
      simp only [certificateMeasure,integerSize,fieldVolume_cons]
      omega
  · simp_all [packCertificate]

theorem parseCertificate_measure (bits : List Bool) (c : Certificate)
    (h : (parseCertificate bits).1 = some c) : certificateMeasure c ≤ bits.length := by
  unfold parseCertificate at h
  cases hp : (EncodingTime.parse bits).1 with
  | none => simp [hp] at h
  | some fields =>
    have hc : (packCertificate fields).1 = some c := by simpa [hp] using h
    exact (packCertificate_measure fields c hc).trans (parse_volume bits fields hp)

lemma source_widths (s : Source) :
    s.products.length ≤ sourceMeasure s ∧ s.declaredCount.length ≤ sourceMeasure s ∧
    s.capacity.length ≤ sourceMeasure s ∧ ComplexityTimeFractions.width s.alpha ≤ sourceMeasure s ∧
    ComplexityTimeFractions.width s.target ≤ sourceMeasure s ∧
    ∀ rv ∈ s.products, ComplexityTimeFractions.width rv.1 ≤ sourceMeasure s ∧
      ComplexityTimeFractions.width rv.2 ≤ sourceMeasure s := by
  have ha := fractionWidth_le_size s.alpha
  have hh := fractionWidth_le_size s.target
  unfold sourceMeasure productsMeasure
  refine ⟨by omega,by omega,by omega,by omega,by omega,?_⟩
  intro rv hr
  have hs := size_mem_le_sum (fun rv : Fraction × Fraction => fractionSize rv.1+fractionSize rv.2) s.products rv hr
  dsimp only at hs
  have h1 := fractionWidth_le_size rv.1
  have h2 := fractionWidth_le_size rv.2
  constructor <;> omega

lemma bitsPositive_cost (bits : List Bool) : (bitsPositive bits).2 ≤ 16*bits.length+3 := by
  simp [bitsPositive,compareBits_cost]
lemma bitsLE_cost (x y : List Bool) : (bitsLE x y).2 ≤ 16*max x.length y.length+3 := by
  simp [bitsLE,compareBits_cost]
lemma bitsEQ_cost (x y : List Bool) : (bitsEQ x y).2 ≤ 16*max x.length y.length+3 := by
  simp [bitsEQ,compareBits_cost]
lemma integerPositive_cost (x : ZBits) :
    (integerPositive x).2 ≤ 48*ComplexityTimeVerifier.width x+24 := by
  have h := zle_cost x zzero
  simpa [integerPositive,zzero,ComplexityTimeVerifier.width] using Nat.add_le_add_right h 2
lemma fractionPositive_cost (x : Fraction) (B : ℕ) (h : ComplexityTimeFractions.width x ≤ B) :
    (fractionPositive x).2 ≤ 64*B+31 := by
  have hd := bitsPositive_cost x.den
  have hn := integerPositive_cost x.num
  have h1 : x.den.length ≤ B := (le_max_right _ _).trans h
  have h2 : ComplexityTimeVerifier.width x.num ≤ B := (le_max_left _ _).trans h
  simp only [fractionPositive]
  omega
lemma alphaUpper_cost (x : Fraction) (B : ℕ) (h : ComplexityTimeFractions.width x ≤ B) :
    (alphaUpper x).2 ≤ 48*B+22 := by
  have hh := zle_cost x.num (x.den,[])
  have h1 : x.den.length ≤ B := (le_max_right _ _).trans h
  have h2 : ComplexityTimeVerifier.width x.num ≤ B := (le_max_left _ _).trans h
  have hd : ComplexityTimeVerifier.width (x.den,[]) = x.den.length := by simp [ComplexityTimeVerifier.width]
  rw [hd] at hh
  exact hh.trans (by gcongr; exact max_le h2 h1)

theorem validateProducts_cost (xs : List (Fraction × Fraction)) (B : ℕ)
    (h : ∀ rv ∈ xs, ComplexityTimeFractions.width rv.1 ≤ B ∧ ComplexityTimeFractions.width rv.2 ≤ B) :
    (validateProducts xs).2 ≤ xs.length*(128*B+70)+1 := by
  induction xs with
  | nil => simp [validateProducts]
  | cons rv xs ih =>
    have hp := h rv (by simp)
    have h1 := fractionPositive_cost rv.1 B hp.1
    have h2 := fractionPositive_cost rv.2 B hp.2
    have ht := ih (fun rv hrv => h rv (by simp [hrv]))
    simp only [validateProducts,List.length_cons]
    nlinarith

theorem validateSource_cost (s : Source) : (validateSource s).2 ≤ 1000*(sourceMeasure s+1)^2 := by
  let S := sourceMeasure s
  have hw := source_widths s
  have hn := FPTASCostSeeds.countBits_cost s.products
  have hnW := FPTASCostSeeds.countBits_width s.products
  have hd := bitsEQ_cost s.declaredCount (FPTASCostSeeds.countBits s.products).1
  have he := bitsPositive_cost (FPTASCostSeeds.countBits s.products).1
  have hk := bitsPositive_cost s.capacity
  have hkr := bitsLE_cost s.capacity (FPTASCostSeeds.countBits s.products).1
  have ha := fractionPositive_cost s.alpha S hw.2.2.2.1
  have hau := alphaUpper_cost s.alpha S hw.2.2.2.1
  have hH := bitsPositive_cost s.target.den
  have hHd : s.target.den.length ≤ S := (le_max_right _ _).trans hw.2.2.2.2.1
  have hp := validateProducts_cost s.products S hw.2.2.2.2.2
  have hm1 : max s.declaredCount.length (FPTASCostSeeds.countBits s.products).1.length ≤ S+1 := by omega
  have hm2 : max s.capacity.length (FPTASCostSeeds.countBits s.products).1.length ≤ S+1 := by omega
  have hns := Nat.mul_self_le_mul_self (show s.products.length+1 ≤ S+1 by omega)
  have hnp := Nat.mul_le_mul_right S hw.1
  change _ ≤ 1000*(S+1)^2
  simp only [validateSource]
  nlinarith [hw.1,hw.2.2.1]

theorem validateCertificate_cost (s : Source) (c : Certificate) :
    (validateCertificate s c).2 ≤ 100*(sourceMeasure s+certificateMeasure c+1) := by
  have h1 := sameLength_cost s.products c.numerators
  have h2 := sameLength_cost c.mask c.numerators
  have h3 := integerPositive_cost c.denominator
  have hn := (source_widths s).1
  have hq := integerWidth_le_size c.denominator
  simp only [validateCertificate,certificateMeasure,tripleMeasure]
  omega

end BalancedAssortments.ComplexityTimeSourceParsing
