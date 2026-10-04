import BalancedAssortments.NPStackSourceVerifierComplete
import BalancedAssortments.NPStackSourceVerifierFieldBounds

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

lemma parseSource_unpack (word : List Bool) (s : Source) (h : (parseSource word).1=some s) :
    ∃ fs,(EncodingTime.parse word).1=some fs ∧ (packSource fs).1=some s := by
  cases hp : (EncodingTime.parse word).1 with
  | none => simp [parseSource,hp] at h
  | some fs => exact ⟨fs,rfl,by simpa [parseSource,hp] using h⟩
lemma parseCertificate_unpack (word : List Bool) (c : Certificate) (h : (parseCertificate word).1=some c) :
    ∃ fs,(EncodingTime.parse word).1=some fs ∧ (packCertificate fs).1=some c := by
  cases hp : (EncodingTime.parse word).1 with
  | none => simp [parseCertificate,hp] at h
  | some fs => exact ⟨fs,rfl,by simpa [parseCertificate,hp] using h⟩

/-- The old polynomial wire witness transfers to the literal tagged guessing
machine with exactly the same length, including every padded field bit. -/
theorem short_tagged_witness (word : List Bool) (h : SourceLanguage word) :
    ∃ sf cf s c,(EncodingTime.parse word).1=some sf ∧
      (packSource sf).1=some s ∧ (packCertificate cf).1=some c ∧ (verifyParsed s c).1=true ∧
      (NPStackFields.dataFields cf).length≤wireCertificatePolynomial.eval word.length ∧
      fieldVolume sf+fieldVolume cf+1≤word.length+wireCertificatePolynomial.eval word.length+1 := by
  obtain ⟨cert,hsize,hacc⟩ := totalVerify_complete_short word h
  cases hs : (parseSource word).1 with
  | none => simp [totalVerify,hs] at hacc
  | some s =>
    cases hc : (parseCertificate cert).1 with
    | none => simp [totalVerify,hs,hc] at hacc
    | some c =>
      have ha : (verifyParsed s c).1=true := by simpa [totalVerify,hs,hc] using hacc
      obtain ⟨sf,hsp,hss⟩:=parseSource_unpack word s hs
      obtain ⟨cf,hcp,hcc⟩:=parseCertificate_unpack cert c hc
      have hlen : (NPStackFields.dataFields cf).length=cert.length := by
        rw [Framing.tagged_wire_length,NPStackFields.parse_sound cert cf hcp]
      have hvs:=parse_volume word sf hsp
      have hvc:=parse_volume cert cf hcp
      exact ⟨sf,cf,s,c,hsp,hss,hcc,ha,hlen.le.trans hsize,by omega⟩

end BalancedAssortments.NPStack.SourceVerifier
