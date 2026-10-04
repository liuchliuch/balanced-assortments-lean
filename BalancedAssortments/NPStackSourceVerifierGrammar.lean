import BalancedAssortments.NPStackSourceVerifierTraceSound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

def parsedSource (header : Fin 8→List Bool) (rs : List NPStackSourcePairing.PairRecord) : Source :=
  ⟨header 0,header 1,⟨(header 2,header 3),header 4⟩,⟨(header 5,header 6),header 7⟩,
    rs.map (fun r=>((decodeRecord r).price,(decodeRecord r).attraction))⟩
def parsedCertificate (header : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord) : Certificate :=
  ⟨(header 0,header 1),rs.map (fun r=>(decodeRecord r).active),rs.map (fun r=>(decodeRecord r).numerator)⟩

lemma parseProducts_records (rs : List NPStackSourcePairing.PairRecord) :
    (parseProducts (rs.flatMap (fun r=>List.ofFn r.1))).1=
      some (rs.map (fun r=>((decodeRecord r).price,(decodeRecord r).attraction))) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simpa [List.ofFn_succ,parseProducts,decodeRecord] using congrArg (Option.map (fun xs=>((decodeRecord r).price,(decodeRecord r).attraction)::xs)) ih

lemma parseTriples_records (rs : List NPStackSourcePairing.PairRecord)
    (hm : ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active) :
    (parseTriples (rs.flatMap (fun r=>List.ofFn r.2))).1=
      some (rs.map (fun r=>(decodeRecord r).active),rs.map (fun r=>(decodeRecord r).numerator)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr:=hm r (by simp)
    rw [NPStackMask.maskValue_parseMask] at hr
    have ht:=ih (by intro x hx;exact hm x (by simp [hx]))
    simp [List.ofFn_succ,decodeRecord] at ht
    simp [List.ofFn_succ,parseTriples,hr,ht,decodeRecord]

lemma packSource_records (header : Fin 8→List Bool) (rs : List NPStackSourcePairing.PairRecord) :
    (packSource (List.ofFn header++rs.flatMap (fun r=>List.ofFn r.1))).1=some (parsedSource header rs) := by
  have h:=parseProducts_records rs
  simp only [List.ofFn_succ] at h
  simpa [List.ofFn_succ,packSource,parsedSource] using h

lemma packCertificate_records (header : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    (hm : ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active) :
    (packCertificate (List.ofFn header++rs.flatMap (fun r=>List.ofFn r.2))).1=some (parsedCertificate header rs) := by
  have h:=parseTriples_records rs hm
  simp only [List.ofFn_succ] at h
  simpa [List.ofFn_succ,packCertificate,parsedCertificate] using h

lemma parsed_sourceRecords (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) :
    sourceRecords (parsedSource hs rs) (parsedCertificate hc rs)=rs.map decodeRecord := by
  unfold sourceRecords parsedSource parsedCertificate
  induction rs with
  | nil => rfl
  | cons r rs ih => simp_all

lemma RowsValid_masks (rs : List NPStackSourcePairing.PairRecord) (s : Registers)
    (hv : RowsValid (rs.map decodeRow) s) :
    ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active := by
  induction rs generalizing s with
  | nil => simp
  | cons r rs ih =>
    rcases hv with ⟨hm,ha,ht⟩
    intro x hx
    rcases List.mem_cons.mp hx with h|h
    · subst x;exact hm
    · exact ih _ ht x h

end BalancedAssortments.NPStack.SourceVerifier
