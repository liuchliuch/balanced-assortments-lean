import BalancedAssortments.DirectVerifierHeader

namespace BalancedAssortments.DirectVerifier
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceParsing

def ShapeValid (s : Source) (c : Certificate) : Prop :=
  c.numerators.length=s.products.length ∧ c.mask.length=c.numerators.length

def shapeGuard (s : Source) (c : Certificate) : Bool :=
  (ComplexityTimeVerifier.sameLength s.products c.numerators).1 &&
    (ComplexityTimeVerifier.sameLength c.mask c.numerators).1

lemma shapeGuard_correct (s : Source) (c : Certificate) : shapeGuard s c=true ↔ ShapeValid s c := by
  simp only [shapeGuard,Bool.and_eq_true,ComplexityTimeVerifier.sameLength_correct,ShapeValid]
  omega

lemma sourceRecords_products (s : Source) (c : Certificate) (h : ShapeValid s c) :
    (sourceRecords s c).map (fun x => (x.price,x.attraction))=s.products := by
  simp only [sourceRecords,List.map_map,Function.comp_def,Prod.mk.eta]
  exact List.map_fst_zip (by simp [h.1,h.2])

lemma sourceRecords_length (s : Source) (c : Certificate) (h : ShapeValid s c) :
    (sourceRecords s c).length=s.products.length := by simp [sourceRecords,h.1,h.2]

lemma sourceRecords_legal (s : Source) (c : Certificate) (h : ShapeValid s c) :
    (sourceRecords s c).all recordLegal=true ↔
      ∀ rv∈s.products,(Valid rv.1 ∧ 0<decode rv.1) ∧ (Valid rv.2 ∧ 0<decode rv.2) := by
  rw [← sourceRecords_products s c h]
  simp only [List.all_eq_true,List.forall_mem_map,recordLegal_correct]

lemma header_products_iff (s : Source) (c : Certificate) :
    (HeaderLegal s c.denominator ∧
      (∀ rv∈s.products,(Valid rv.1 ∧ 0<decode rv.1) ∧ (Valid rv.2 ∧ 0<decode rv.2))) ↔
      LegalSource s ∧ 0<zvalue c.denominator := by
  unfold HeaderLegal LegalSource
  tauto

/-- Interleave local source/witness checking with a single arithmetic pass,
then make the short balance pass. Shape checking remains explicit. -/
def streamingVerifyParsed (s : Source) (c : Certificate) : Bool :=
  if shapeGuard s c then
    let xs := sourceRecords s c
    headerGuard s c.denominator (countRecordBits xs) && xs.all recordLegal &&
      streamCheck s.alpha s.target s.capacity c.denominator xs
  else false

theorem streamingVerifyParsed_eq (s : Source) (c : Certificate) :
    streamingVerifyParsed s c=(verifyParsed s c).1 := by
  rw [← verifyParsedDirect_eq]
  apply Bool.eq_iff_iff.mpr
  by_cases hshape : shapeGuard s c=true
  · have h := (shapeGuard_correct s c).mp hshape
    have hcount : zvalue (countRecordBits (sourceRecords s c))=(s.products.length : ℤ) := by
      rw [countRecordBits_value,sourceRecords_length s c h]
    simp only [streamingVerifyParsed,hshape,if_true,Bool.and_eq_true,
      headerGuard_correct s c.denominator _ hcount,sourceRecords_legal s c h,
      streamCheck_eq,header_products_iff]
    have hc : (validateCertificate s c).1=true ↔ 0<zvalue c.denominator := by
      rw [validateCertificate_correct]
      simp only [h.1,h.2,true_and]
    have hq : positive c.denominator=true ↔ 0<zvalue c.denominator := positive_correct _
    have hs : (validateSource s).1=true ↔ LegalSource s := validateSource_correct s
    by_cases hss : (validateSource s).1=true <;> by_cases hcc : (validateCertificate s c).1=true <;>
      simp_all [verifyParsedDirect,positive]
  · have h : ¬ShapeValid s c := by simpa only [shapeGuard_correct] using hshape
    have hc : (validateCertificate s c).1≠true := by
      intro hc
      have hh := (validateCertificate_correct s c).mp hc
      exact h ⟨hh.1,hh.2.1⟩
    simp [streamingVerifyParsed,hshape,verifyParsedDirect,hc]

end BalancedAssortments.DirectVerifier
