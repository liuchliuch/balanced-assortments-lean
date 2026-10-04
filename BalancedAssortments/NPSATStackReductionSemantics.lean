import BalancedAssortments.NPSATStackGadgetSemantics
import BalancedAssortments.NPSATStackGadgetComplete
import BalancedAssortments.NPSATStackPrepareCorrect

/-! Exact total-language semantics of the operational 3CNF gadget output.
Catalogue reversal changes digit positions, not the indexed Subset Sum problem.
The zero-dimensional satisfiable input and every malformed branch are explicit. -/
noncomputable section
namespace BalancedAssortments.NPSATStackReduction
open NPCNF NPCNF.Encoding NPSATSubsetSum NPSATStackSemantics

lemma gadget_result_correct (raw : Raw) (hv : raw.decode.Valid) (ht : ThreeCNF raw.decode.formula) :
    PositiveSubsetSumLanguage (NPSATStackGadget.result raw.catalog raw.formula) ↔ raw.decode.Sat := by
  change PositiveSubsetSumLanguage (NPSATStackSlack.patchedWire raw.catalog.length raw.formula.length (successWire raw)) ↔ _
  unfold NPSATStackSlack.patchedWire
  split_ifs with hz
  · have hf : raw.formula=[] := List.length_eq_zero.mp hz.2
    simp [fixedYes_mem,Catalogued.Sat,Raw.decode,hf,Sat]
  · exact successWire_correct raw hv ht (by rintro ⟨hc,hf⟩;apply hz;simp [hc,hf])

lemma reversed_valid (raw : Raw) (hv : raw.decode.Valid) :
    (Raw.mk raw.catalog.reverse raw.formula).decode.Valid := by
  constructor
  · simpa [Raw.decode,List.map_reverse] using hv.1
  · intro c hc l hl
    simpa [Raw.decode,List.map_reverse] using hv.2 c hc l hl

lemma reversed_result_correct (raw : Raw) (hv : raw.decode.Valid) (ht : ThreeCNF raw.decode.formula) :
    PositiveSubsetSumLanguage (NPSATStackGadget.result raw.catalog.reverse raw.formula) ↔ raw.decode.Sat :=
  gadget_result_correct ⟨raw.catalog.reverse,raw.formula⟩ (reversed_valid raw hv) ht

def reduction (bits : List Bool) : List Bool :=
  match (parse bits).1 with
  | none => fixedNo
  | some raw => if (validate raw).1 && (checkThree raw.formula).1 then
      NPSATStackGadget.result raw.catalog.reverse raw.formula else fixedNo

lemma reduction_of_good (bits : List Bool) (raw : Raw) (hp : (parse bits).1=some raw)
    (hv : raw.decode.Valid) (ht : ThreeCNF raw.decode.formula) :
    reduction bits=NPSATStackGadget.result raw.catalog.reverse raw.formula := by
  have hv' := (validate_correct raw).mpr hv
  have ht' := (checkThree_correct raw.formula).mpr ht
  simp [reduction,hp,hv',ht']

lemma reduction_of_not_good (bits : List Bool) (hn : ¬NPSATStackPrepare.GoodInput bits) :
    reduction bits=fixedNo := by
  unfold reduction
  cases hp : (parse bits).1 with
  | none => rfl
  | some raw =>
    dsimp only
    split_ifs with h
    · have hh : (validate raw).1=true ∧ (checkThree raw.formula).1=true := by simpa only [Bool.and_eq_true] using h
      exact False.elim (hn ⟨raw,hp,(validate_correct raw).mp hh.1,(checkThree_correct raw.formula).mp hh.2⟩)
    · rfl

theorem reduction_correct (bits : List Bool) :
    PositiveSubsetSumLanguage (reduction bits) ↔ ThreeCNFLanguage bits := by
  by_cases hg : NPSATStackPrepare.GoodInput bits
  · obtain ⟨raw,hp,hv,ht⟩ := hg
    rw [reduction_of_good bits raw hp hv ht,reversed_result_correct raw hv ht]
    simp [ThreeCNFLanguage,hp,hv,ht]
  · rw [reduction_of_not_good bits hg]
    have hn : ¬ThreeCNFLanguage bits := by
      rintro ⟨raw,hp,hv,ht,_⟩
      exact hg ⟨raw,hp,hv,ht⟩
    simp [fixedNo_not_mem,hn]

theorem three_iff_reduction (bits : List Bool) :
    ThreeCNFLanguage bits ↔ PositiveSubsetSumLanguage (reduction bits) := (reduction_correct bits).symm
end BalancedAssortments.NPSATStackReduction
