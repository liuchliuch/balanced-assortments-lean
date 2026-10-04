import BalancedAssortments.ComplexityTimeTotalBounds

namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline

def wireCertificateBound (L : ℕ) : ℕ := L*(2*certificateBound L+5)+2*certificateBound L+2
noncomputable def wireCertificatePolynomial : Polynomial ℕ :=
  Polynomial.X*(2*certificatePolynomial+5)+2*certificatePolynomial+2

lemma wireCertificatePolynomial_eval (L : ℕ) :
    wireCertificatePolynomial.eval L = wireCertificateBound L := by
  simp [wireCertificatePolynomial,wireCertificateBound,certificatePolynomial_eval]

lemma certificateBound_mono {a b : ℕ} (h : a ≤ b) : certificateBound a ≤ certificateBound b := by
  unfold certificateBound witnessWidth
  gcongr

/-- Every legal serialized real yes-instance has a polynomial-length serialized
certificate accepted by the total parser, validator and raw binary checker. -/
theorem totalVerify_complete_short (sourceBits : List Bool) (h : SourceLanguage sourceBits) :
    ∃ certificateBits, certificateBits.length ≤ wireCertificatePolynomial.eval sourceBits.length ∧
      (totalVerify sourceBits certificateBits).1 = true := by
  obtain ⟨s,hs,hlegal,hyes⟩ := h
  have hv := legal_verifier_conditions s hlegal
  obtain ⟨mask,p,q,hm,hacc,hsize⟩ := source_has_short_binary_certificate s.attractions s.prices
    s.alpha s.target s.capacity (by simp [Source.attractions]) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hyes
  have hq : 0 < q := by
    exact ((verifySourceSized_correct s.attractions s.prices s.alpha s.target s.capacity mask
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 p q).mp hacc).1
  have hac : (verifySource s.attractions s.prices s.alpha s.target s.capacity mask
      (encodedNumerators p) (zencode q)).1 = true := by
    simpa only [verifySource,Source.attractions,List.length_map] using hacc
  have hr := verifyParsed_from_accepted hlegal rfl mask p q hm hq hac
  have hL := (sourceInputSize_le_measure s).trans (parseSource_measure sourceBits s hs)
  have hn := (source_widths s).1.trans (parseSource_measure sourceBits s hs)
  have hb := certificateBound_mono hL
  have hsize' : (certificateBits mask p q).length ≤ certificateBound sourceBits.length := hsize.trans hb
  have hp : ∀ j, (p j).natAbs.size ≤ certificateBound sourceBits.length := by
    intro j
    have hj : (p j).natAbs.size ≤ ∑ k, (p k).natAbs.size := Finset.single_le_sum (f := fun k => (p k).natAbs.size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [certificateBits_length] at hsize'
    omega
  have hqs : q.natAbs.size ≤ certificateBound sourceBits.length := by
    rw [certificateBits_length] at hsize'
    omega
  have hwire := certificateEncoding_short mask p q hm hp hqs
  refine ⟨certificateEncoding mask p q,?_,?_⟩
  · rw [wireCertificatePolynomial_eval]
    unfold wireCertificateBound
    exact hwire.trans (by gcongr)
  · have hc := parseCertificate_encoded mask p q hm
    simp only [totalVerify,hs,hc]
    exact hr

/-- A complete polynomial-certificate characterization of this particular total
bitstring language. The operational bit/list cost theorem is separate; no
machine-model NP predicate is silently substituted by this characterization. -/
theorem source_language_iff_short_accepted (sourceBits : List Bool) :
    SourceLanguage sourceBits ↔ ∃ certificateBits,
      certificateBits.length ≤ wireCertificatePolynomial.eval sourceBits.length ∧
      (totalVerify sourceBits certificateBits).1 = true :=
  ⟨totalVerify_complete_short sourceBits,
    fun ⟨certificate,_,h⟩ => totalVerify_sound sourceBits certificate h⟩

end BalancedAssortments.ComplexityTimeSourceParsing
