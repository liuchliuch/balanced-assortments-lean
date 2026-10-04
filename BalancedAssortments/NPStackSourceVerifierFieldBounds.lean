import BalancedAssortments.NPStackSourceVerifierGrammarPair
import BalancedAssortments.NPStackSourceVerifierTraceBound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

lemma prefix_field_member {m : ℕ} (header : Fin m→List Bool) (tail : List (List Bool)) (i : Fin m) :
    header i∈List.ofFn header++tail := List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

lemma record_source_member (hs : Fin 8→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    (r : NPStackSourcePairing.PairRecord) (hr : r∈rs) (i : Fin 6) :
    r.1 i∈List.ofFn hs++rs.flatMap (fun r=>List.ofFn r.1) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨r,hr,List.mem_ofFn.mpr ⟨i,rfl⟩⟩)
lemma record_certificate_member (hc : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    (r : NPStackSourcePairing.PairRecord) (hr : r∈rs) (i : Fin 3) :
    r.2 i∈List.ofFn hc++rs.flatMap (fun r=>List.ofFn r.2) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨r,hr,List.mem_ofFn.mpr ⟨i,rfl⟩⟩)

lemma paired_fields_bound (sf cf : List (List Bool)) (hs : Fin 8→List Bool) (hc : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord)
    (hfs : sf=List.ofFn hs++rs.flatMap (fun r=>List.ofFn r.1))
    (hfc : cf=List.ofFn hc++rs.flatMap (fun r=>List.ofFn r.2)) {L : ℕ}
    (hL : fieldVolume sf+fieldVolume cf+1≤L) :
    (∀ i,(hs i).length≤L) ∧ (∀ i,(hc i).length≤L) ∧
    (∀ r∈rs,recordWidth (decodeRecord r)≤L ∧ (r.2 0).length≤L) ∧ rs.length≤L := by
  have hsf : ∀ x∈sf,x.length≤L := by intro x hx;have hh:=field_member_length sf x hx;omega
  have hcf : ∀ x∈cf,x.length≤L := by intro x hx;have hh:=field_member_length cf x hx;omega
  refine ⟨?_,?_,?_,?_⟩
  · intro i;apply hsf;rw [hfs];exact prefix_field_member _ _ _
  · intro i;apply hcf;rw [hfc];exact prefix_field_member _ _ _
  · intro r hr
    have ha : ∀ i,(r.1 i).length≤L := by intro i;apply hsf;rw [hfs];exact record_source_member _ _ _ hr i
    have hb : ∀ i,(r.2 i).length≤L := by intro i;apply hcf;rw [hfc];exact record_certificate_member _ _ _ hr i
    refine ⟨?_,hb 0⟩
    have h0:=ha 0;have h1:=ha 1;have h2:=ha 2;have h3:=ha 3;have h4:=ha 4;have h5:=ha 5
    have hp:=hb 1;have hn:=hb 2
    unfold recordWidth ComplexityTimeFractions.width width decodeRecord
    dsimp only
    omega
  · have hn:=field_count_le_volume sf
    rw [hfs,List.length_append,List.length_ofFn,List.length_flatMap] at hn
    simp only [List.length_ofFn,List.map_const',List.sum_replicate,smul_eq_mul] at hn
    rw [←hfs] at hn
    omega

lemma initial_width (hs : Fin 8→List Bool) (hc : Fin 2→List Bool) {L : ℕ}
    (hL : 1≤L) (hhs : ∀ i,(hs i).length≤L) (hhc : ∀ i,(hc i).length≤L) :
    ∀ k,width (Whole.initialRegisters hs hc k)≤L := by
  intro k
  have h0:=hhs 0;have h1:=hhs 1;have h2:=hhs 2;have h3:=hhs 3
  have h4:=hhs 4;have h5:=hhs 5;have h6:=hhs 6;have h7:=hhs 7
  have hc0:=hhc 0;have hc1:=hhc 1
  cases k <;> simp [Whole.initialRegisters,width,zOne,zzero] <;> omega

end BalancedAssortments.NPStack.SourceVerifier
