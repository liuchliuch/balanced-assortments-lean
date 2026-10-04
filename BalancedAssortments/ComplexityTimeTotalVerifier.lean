import BalancedAssortments.ComplexityTimeCertificateParsing
import BalancedAssortments.ComplexityTimeSourceRawCorrect

/-! A total serialized source/certificate verifier. Malformed formats and illegal
source parameters are rejected explicitly; target revenue may have either sign. -/
namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline DecisionPolyhedron

def Source.attractions (s : Source) : List Fraction := s.products.map Prod.snd
def Source.prices (s : Source) : List Fraction := s.products.map Prod.fst

def SourceYes (s : Source) : Prop := ∃ x : Fin s.products.length → ℝ,
  Sales.CompactFeasible (fun j => (decodedValues s.attractions j : ℝ)) x (value s.capacity) ∧
  Sales.Balanced (decode s.alpha : ℝ) x ∧
  (decode s.target : ℝ) ≤ Sales.objective (fun j => (decodedValues s.prices j : ℝ)) x

/-- The target language is defined independently by parsed legal model instances
and existence of an actual feasible real sales vector. -/
def SourceLanguage (bits : List Bool) : Prop :=
  ∃ s, (parseSource bits).1 = some s ∧ LegalSource s ∧ SourceYes s

lemma lookup_member {α : Type*} (fallback : α) (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (lookup fallback xs i).1 ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [lookup]
    | succ i =>
      have hh := ih i (by simpa using hi)
      exact List.mem_cons_of_mem x hh

lemma legal_verifier_conditions (s : Source) (h : LegalSource s) :
    (∀ j : Fin s.products.length, Valid (lookup zero s.attractions j.val).1 ∧
      0 < decode (lookup zero s.attractions j.val).1) ∧
    (∀ j : Fin s.products.length, Valid (lookup zero s.prices j.val).1) ∧
    Valid s.alpha ∧ Valid s.target := by
  rcases h with ⟨_,_,_,_,ha,_,hH,hprod⟩
  refine ⟨?_,?_,ha.1,hH⟩
  · intro j
    have hm := lookup_member zero s.attractions j.val (by simpa [Source.attractions] using j.isLt)
    obtain ⟨rv,hrv,he⟩ := List.mem_map.mp hm
    simpa only [he] using (hprod rv hrv).2
  · intro j
    have hm := lookup_member zero s.prices j.val (by simpa [Source.prices] using j.isLt)
    obtain ⟨rv,hrv,he⟩ := List.mem_map.mp hm
    simpa only [he] using (hprod rv hrv).1.1

def verifyParsed (s : Source) (c : Certificate) : Bool × ℕ :=
  let sv := validateSource s
  let cv := validateCertificate s c
  if sv.1 && cv.1 then
    let checked := verifySource s.attractions s.prices s.alpha s.target s.capacity c.mask c.numerators c.denominator
    (checked.1,sv.2+cv.2+checked.2+4*s.products.length+8)
  else (false,sv.2+cv.2+4)

/-- The total verifier executes both parsers and every source/certificate
legality check before it runs the substantive row-generation checker. -/
def totalVerify (sourceBits certificateBits : List Bool) : Bool × ℕ :=
  let s := parseSource sourceBits
  let c := parseCertificate certificateBits
  match s.1,c.1 with
  | some sd,some cd => let r := verifyParsed sd cd; (r.1,s.2+c.2+r.2+4)
  | _,_ => (false,s.2+c.2+4)

theorem verifyParsed_sound (s : Source) (c : Certificate) (h : (verifyParsed s c).1 = true) :
    LegalSource s ∧ SourceYes s := by
  unfold verifyParsed at h
  dsimp only at h
  split_ifs at h with guard
  · have hg : (validateSource s).1 = true ∧ (validateCertificate s c).1 = true := by
      simpa only [Bool.and_eq_true] using guard
    have hs := (validateSource_correct s).mp hg.1
    have hc := (validateCertificate_correct s c).mp hg.2
    have hv := legal_verifier_conditions s hs
    have hraw : (verifySourceSized s.products.length s.attractions s.prices s.alpha s.target
        s.capacity c.mask c.numerators c.denominator).1 = true := by
      simpa only [verifySource,Source.attractions,List.length_map] using h
    have hh := (verifySourceSized_raw_correct s.attractions s.prices s.alpha s.target s.capacity c.mask
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 c.numerators c.denominator hc.1).mp hraw
    refine ⟨hs,(fun j => (rawCertificateValues (n := s.products.length) c.numerators j : ℝ)/(zvalue c.denominator : ℝ)),?_⟩
    exact rows_source_sound (decodedValues s.attractions) (decodedValues s.prices)
      (decode s.alpha) (decode s.target) (value s.capacity) (support c.mask s.products.length) _ hh.2

theorem totalVerify_sound (sourceBits certificateBits : List Bool)
    (h : (totalVerify sourceBits certificateBits).1 = true) : SourceLanguage sourceBits := by
  unfold totalVerify at h
  cases hs : (parseSource sourceBits).1 with
  | none => simp [hs] at h
  | some s =>
    cases hc : (parseCertificate certificateBits).1 with
    | none => simp [hs,hc] at h
    | some c =>
      have hh : (verifyParsed s c).1 = true := by simpa [hs,hc] using h
      exact ⟨s,hs,verifyParsed_sound s c hh⟩

lemma verifyParsed_from_accepted {s : Source} (hs : LegalSource s) {n : ℕ}
    (hn : n = s.products.length) (mask : List Bool) (p : Fin n → ℤ) (q : ℤ)
    (hm : mask.length = n) (hq : 0 < q)
    (hacc : (verifySource s.attractions s.prices s.alpha s.target s.capacity mask (encodedNumerators p) (zencode q)).1 = true) :
    (verifyParsed s ⟨zencode q,mask,encodedNumerators p⟩).1 = true := by
  have hv := (validateSource_correct s).mpr hs
  have hc : (validateCertificate s ⟨zencode q,mask,encodedNumerators p⟩).1 = true := by
    apply (validateCertificate_correct s _).mpr
    simp only [encodedNumerators,List.length_ofFn,zencode_value]
    exact ⟨hn,hm,hq⟩
  simp only [verifyParsed,hv,hc,Bool.true_and,↓reduceIte]
  exact hacc

/-- Completeness constructs actual certificate bytes for every legal parsed
source yes-instance, not merely a semantic certificate record. -/
theorem totalVerify_complete (sourceBits : List Bool) (h : SourceLanguage sourceBits) :
    ∃ certificateBits, (totalVerify sourceBits certificateBits).1 = true := by
  obtain ⟨s,hs,hlegal,hyes⟩ := h
  have hv := legal_verifier_conditions s hlegal
  obtain ⟨mask,p,q,hm,hacc,hsize⟩ := source_has_short_binary_certificate s.attractions s.prices
    s.alpha s.target s.capacity (by simp [Source.attractions]) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hyes
  have hq : 0 < q := by
    have hh := (verifySourceSized_correct s.attractions s.prices s.alpha s.target s.capacity mask
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 p q).mp hacc
    exact hh.1
  have hac : (verifySource s.attractions s.prices s.alpha s.target s.capacity mask
      (encodedNumerators p) (zencode q)).1 = true := by
    simpa only [verifySource,Source.attractions,List.length_map] using hacc
  have hr := verifyParsed_from_accepted hlegal rfl mask p q hm hq hac
  refine ⟨certificateEncoding mask p q,?_⟩
  have hc := parseCertificate_encoded mask p q hm
  simp only [totalVerify,hs,hc]
  exact hr

/-- Exact characterization of the fully serialized target language. This does
not assert a machine-defined NP-class theorem or a Subset Sum hardness axiom. -/
theorem total_language_iff_accepted (sourceBits : List Bool) :
    SourceLanguage sourceBits ↔ ∃ certificateBits, (totalVerify sourceBits certificateBits).1 = true :=
  ⟨totalVerify_complete sourceBits,fun ⟨certificate,h⟩ => totalVerify_sound sourceBits certificate h⟩

end BalancedAssortments.ComplexityTimeSourceParsing
