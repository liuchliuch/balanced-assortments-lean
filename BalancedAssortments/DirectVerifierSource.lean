import BalancedAssortments.DirectVerifierChecker

namespace BalancedAssortments.DirectVerifier
open scoped BigOperators
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions
open ComplexityTimeSourceParsing ComplexityTimeSourceRows ComplexityTimeSourcePipeline

def sourceRecords (s : Source) (c : Certificate) : List WitnessRecord :=
  (s.products.zip (c.numerators.zip c.mask)).map fun x => ⟨x.1.1,x.1.2,x.2.1,x.2.2⟩

def sourceAttraction (s : Source) (i : Fin s.products.length) : Fraction := (lookup zero s.attractions i).1
def sourcePrice (s : Source) (i : Fin s.products.length) : Fraction := (lookup zero s.prices i).1
def sourceNumerator (s : Source) (c : Certificate) (i : Fin s.products.length) : ZBits := c.numerators.getD i zzero
def sourceMask (s : Source) (c : Certificate) (i : Fin s.products.length) : Bool := (lookup false c.mask i).1

lemma sourceRecords_eq (s : Source) (c : Certificate)
    (hp : c.numerators.length=s.products.length) (hm : c.mask.length=c.numerators.length) :
    sourceRecords s c=vectorRecords (sourceAttraction s) (sourcePrice s) (sourceNumerator s c) (sourceMask s c) := by
  apply List.ext_getElem
  · simp [sourceRecords,vectorRecords,hp,hm]
  · intro i hi hj
    have hip : i<s.products.length := by simpa [vectorRecords] using hj
    have hin : i<c.numerators.length := by omega
    have him : i<c.mask.length := by omega
    have hiv : i<s.attractions.length := by simpa [Source.attractions] using hip
    have hir : i<s.prices.length := by simpa [Source.prices] using hip
    simp only [sourceRecords,List.getElem_map,List.getElem_zip,vectorRecords,List.getElem_ofFn,
      sourceAttraction,sourcePrice,sourceNumerator,sourceMask,lookup_value]
    rw [List.getD_eq_getElem _ _ hiv,List.getD_eq_getElem _ _ hir,
      List.getD_eq_getElem _ _ hin,List.getD_eq_getElem _ _ him]
    simp only [Source.prices,Source.attractions,List.getElem_map]

lemma sourceNumerator_value (s : Source) (c : Certificate) (i : Fin s.products.length) :
    zvalue (sourceNumerator s c i)=rawCertificateValues c.numerators i := by
  simp only [sourceNumerator,rawCertificateValues,List.getD_eq_getElem?_getD]

/-- Exact equality with the existing row-matrix verifier under its existing
source-domain and dimension preconditions. No certificate representation is
restricted: signed redundant encodings of p and q remain accepted. -/
theorem checkRecords_eq_verifySource (s : Source) (c : Certificate) (hs : LegalSource s)
    (hc : (validateCertificate s c).1=true) :
    ((!((zle c.denominator zzero).1)) && checkRecords s.alpha s.target s.capacity c.denominator (sourceRecords s c)) =
      (verifySource s.attractions s.prices s.alpha s.target s.capacity c.mask c.numerators c.denominator).1 := by
  have hv := legal_verifier_conditions s hs
  have hc' := (validateCertificate_correct s c).mp hc
  have hαnum : 0≤zvalue s.alpha.num := (numerator_positive s.alpha hs.2.2.2.2.1.1 hs.2.2.2.2.1.2).le
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true]
  have hq : (!((zle c.denominator zzero).1))=true ↔ 0<zvalue c.denominator := by
    have hh := zle_correct c.denominator zzero
    simp only [zzero_value] at hh
    cases he : (zle c.denominator zzero).1 <;> simp_all <;> omega
  rw [hq,sourceRecords_eq s c hc'.1 hc'.2.1,checkRecords_correct,
    clearedMax_iff _ _ _ _ _ _ _ _ hαnum]
  unfold verifySource
  rw [show s.attractions.length=s.products.length by simp [Source.attractions]]
  change (0<zvalue c.denominator ∧ _) ↔
    (verifySourceSized s.products.length s.attractions s.prices s.alpha s.target
      s.capacity c.mask c.numerators c.denominator).1=true
  rw [verifySourceSized_raw_correct _ _ _ _ _ _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 _ _ hc'.1]
  apply and_congr_right
  intro hpositive
  rw [cleared_iff_source_rows (sourceAttraction s) (sourcePrice s) s.alpha s.target
    (value s.capacity) (Finset.univ.filter (fun i => sourceMask s c i))
    (fun i => zvalue (sourceNumerator s c i)) (zvalue c.denominator)
    hpositive hv.1 hv.2.1 hv.2.2.1 hv.2.2.2]
  simp only [sourceAttraction,sourcePrice,sourceNumerator_value,sourceMask,support]
  rfl

def verifyParsedDirect (s : Source) (c : Certificate) : Bool :=
  if (validateSource s).1 && (validateCertificate s c).1 then
    !((zle c.denominator zzero).1) && checkRecords s.alpha s.target s.capacity c.denominator (sourceRecords s c)
  else false

theorem verifyParsedDirect_eq (s : Source) (c : Certificate) :
    verifyParsedDirect s c=(verifyParsed s c).1 := by
  unfold verifyParsedDirect verifyParsed
  dsimp only
  by_cases h : ((validateSource s).1 && (validateCertificate s c).1)=true
  · rw [if_pos h,if_pos h]
    have hh : (validateSource s).1=true ∧ (validateCertificate s c).1=true := by simpa using h
    exact checkRecords_eq_verifySource s c ((validateSource_correct s).mp hh.1) hh.2
  · simp [h]

def totalVerifyDirect (sourceBits certificateBits : List Bool) : Bool :=
  match (parseSource sourceBits).1,(parseCertificate certificateBits).1 with
  | some s,some c => verifyParsedDirect s c
  | _,_ => false

theorem totalVerifyDirect_eq (sourceBits certificateBits : List Bool) :
    totalVerifyDirect sourceBits certificateBits=(totalVerify sourceBits certificateBits).1 := by
  unfold totalVerifyDirect totalVerify
  cases hs : (parseSource sourceBits).1 <;> cases hc : (parseCertificate certificateBits).1 <;>
    simp [hs,hc,verifyParsedDirect_eq]

/-- The direct division-free checker preserves exactly the total source
language and the already-proved serialized polynomial certificate bound. -/
theorem source_language_iff_direct_short (sourceBits : List Bool) :
    SourceLanguage sourceBits ↔ ∃ certificateBits,
      certificateBits.length≤wireCertificatePolynomial.eval sourceBits.length ∧
      totalVerifyDirect sourceBits certificateBits=true := by
  simp only [totalVerifyDirect_eq]
  exact source_language_iff_short_accepted sourceBits

end BalancedAssortments.DirectVerifier
