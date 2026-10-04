import BalancedAssortments.NPStackSourceVerifierGrammarRecover
import BalancedAssortments.NPStackSourceVerifierSemantics

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

/-- Successful original parsers and the original dimension check yield the
same raw header/paired-record streams expected by the concrete machine. -/
theorem parsed_fields_pair (sf cf : List (List Bool)) (s : Source) (c : Certificate)
    (hs : (packSource sf).1=some s) (hc : (packCertificate cf).1=some c)
    (hlen : c.numerators.length=s.products.length) :
    ∃ sh : Fin 8→List Bool,∃ ch : Fin 2→List Bool,∃ rs : List NPStackSourcePairing.PairRecord,
      sf=List.ofFn sh++rs.flatMap (fun r=>List.ofFn r.1) ∧
      cf=List.ofFn ch++rs.flatMap (fun r=>List.ofFn r.2) ∧
      parsedSource sh rs=s ∧ parsedCertificate ch rs=c ∧
      ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active := by
  obtain ⟨sh,xs,hxs,hxl⟩ := packSource_chunks sf s hs
  obtain ⟨ch,ys,hys,hyl,hgood⟩ := packCertificate_chunks cf c hc
  have hl : xs.length=ys.length := by omega
  let rs:=xs.zip ys
  have hx : rs.map Prod.fst=xs := List.map_fst_zip (by omega)
  have hy : rs.map Prod.snd=ys := List.map_snd_zip (by omega)
  have hsf : sf=List.ofFn sh++rs.flatMap (fun r=>List.ofFn r.1) := by
    rw [hxs,←hx,List.flatMap_map]
  have hcf : cf=List.ofFn ch++rs.flatMap (fun r=>List.ofFn r.2) := by
    rw [hys,←hy,List.flatMap_map]
  have hm : ∀ r∈rs,NPStackMask.maskValue (r.2 0)=some (decodeRecord r).active := by
    intro r hr
    have hh : r.2∈ys := by rw [←hy];exact List.mem_map.mpr ⟨r,hr,rfl⟩
    exact hgood r.2 hh
  refine ⟨sh,ch,rs,hsf,hcf,?_,?_,hm⟩
  · have hh := packSource_records sh rs
    rw [←hsf,hs] at hh
    exact (Option.some.inj hh).symm
  · have hh := packCertificate_records ch rs hm
    rw [←hcf,hc] at hh
    exact (Option.some.inj hh).symm

end BalancedAssortments.NPStack.SourceVerifier
