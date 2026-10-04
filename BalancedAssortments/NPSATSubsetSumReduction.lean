import BalancedAssortments.NPSATSubsetSumConstructCorrect
import BalancedAssortments.NPSATSubsetSumPositive
import BalancedAssortments.NPSATSubsetSumConstructCost
import BalancedAssortments.NPCNFThreeReduction

namespace BalancedAssortments.NPSATSubsetSum
open NPCNF NPCNF.Encoding ComplexityTimeBinary ComplexityTimeReduction

/-- Positive-integer Subset Sum as a total language of self-delimiting bitstrings.
The first field is the target and remaining fields are indexed list items. -/
def PositiveSubsetSumLanguage (bits : List Bool) : Prop :=
  match (EncodingTime.parse bits).1 with
  | some (target::items) => 0<value target ∧ (∀ x ∈ items,0<value x) ∧
      ListSubsetSum (items.map value) (value target)
  | _ => False

lemma serialized_subset_sum (target : List Bool) (items : List (List Bool)) :
    PositiveSubsetSumLanguage (serializeFields (target::items)).1 ↔
      0<value target ∧ (∀ x ∈ items,0<value x) ∧ ListSubsetSum (items.map value) (value target) := by
  rw [serializeFields_correct]
  unfold PositiveSubsetSumLanguage
  rw [(EncodingTime.parse_encoded _).1]
  simp only [List.map_cons,value_bits,List.map_map,Function.comp_def]
  simp

def fixedYes : List Bool := ComplexityEncoding.encodeFields [1,1]
def fixedNo : List Bool := ComplexityEncoding.encodeFields [1,2]

lemma fixedYes_mem : PositiveSubsetSumLanguage fixedYes := by
  unfold PositiveSubsetSumLanguage fixedYes
  rw [(EncodingTime.parse_encoded _).1]
  simp only [List.map_cons,List.map_nil,value_bits]
  refine ⟨by decide,by simp [value],?_⟩
  exact ⟨[1],List.Sublist.refl _,by simp⟩

lemma fixedNo_not_mem : ¬ PositiveSubsetSumLanguage fixedNo := by
  unfold PositiveSubsetSumLanguage fixedNo
  rw [(EncodingTime.parse_encoded _).1]
  simp only [List.map_cons,List.map_nil,value_bits]
  rintro ⟨_,_,selected,hs,he⟩
  rcases List.sublist_singleton.mp hs with rfl | rfl <;> simp at he

/-- Total raw-instance stage: invalid instances become a fixed positive no;
the zero-dimensional valid instance becomes a fixed positive yes. -/
def reduceRaw (raw : Raw) : List Bool × ℕ :=
  let legal := validate raw
  let three := checkThree raw.formula
  if legal.1 && three.1 then
    if raw.catalog=[] ∧ raw.formula=[] then (fixedYes,legal.2+three.2+20)
    else
      let gadget := construct raw
      let emitted := serializeFields (gadget.1.1::gadget.1.2)
      (emitted.1,legal.2+three.2+gadget.2+emitted.2+10)
  else (fixedNo,legal.2+three.2+12)

/-- Actual input parser, all validation, gadget arithmetic and serialization. -/
def reduceThree (bits : List Bool) : List Bool × ℕ :=
  let parsed := NPCNF.Encoding.parse bits
  match parsed.1 with
  | none => (fixedNo,parsed.2+12)
  | some raw => let out := reduceRaw raw; (out.1,parsed.2+out.2+4)

lemma construct_positive (raw : Raw) (h : raw.decode.Valid)
    (hne : ¬(raw.catalog=[] ∧ raw.formula=[])) :
    0<value (construct raw).1.1 ∧ ∀ x ∈ (construct raw).1.2,0<value x := by
  have hdim : 0<raw.catalog.length+raw.formula.length := by
    by_contra hz
    have hz' : raw.catalog.length=0 ∧ raw.formula.length=0 := by omega
    exact hne ⟨List.length_eq_zero_iff.mp hz'.1,List.length_eq_zero_iff.mp hz'.2⟩
  refine ⟨by rw [construct_target];exact targetValue_pos hdim,?_⟩
  intro x hx
  have hm : value x ∈ (construct raw).1.2.map value := List.mem_map.mpr ⟨x,hx,rfl⟩
  rw [construct_items raw h] at hm
  obtain ⟨item,_,he⟩ := List.mem_map.mp hm
  rw [← he]
  exact itemValue_pos _ _

theorem reduceRaw_correct (raw : Raw) :
    PositiveSubsetSumLanguage (reduceRaw raw).1 ↔ raw.decode.Valid ∧ ThreeCNF raw.decode.formula ∧ raw.decode.Sat := by
  unfold reduceRaw
  dsimp only
  split_ifs with hg hz
  · have he : raw.decode.Sat := by
      simp [Raw.decode,hz.2,Catalogued.Sat,NPCNF.empty_formula_sat]
    have hv := (validate_correct raw).mp (show (validate raw).1=true from (by simpa only [Bool.and_eq_true] using hg : (validate raw).1=true ∧ (checkThree raw.formula).1=true).1)
    have ht := (checkThree_correct raw.formula).mp (show (checkThree raw.formula).1=true from (by simpa only [Bool.and_eq_true] using hg : (validate raw).1=true ∧ (checkThree raw.formula).1=true).2)
    exact iff_of_true fixedYes_mem ⟨hv,ht,he⟩
  · have hv := (validate_correct raw).mp (show (validate raw).1=true from (by simpa only [Bool.and_eq_true] using hg : (validate raw).1=true ∧ (checkThree raw.formula).1=true).1)
    have ht := (checkThree_correct raw.formula).mp (show (checkThree raw.formula).1=true from (by simpa only [Bool.and_eq_true] using hg : (validate raw).1=true ∧ (checkThree raw.formula).1=true).2)
    have hp := construct_positive raw hv hz
    rw [serialized_subset_sum]
    have hs := construct_correct raw hv ht
    exact ⟨fun h => ⟨hv,ht,hs.mpr h.2.2⟩,fun h => ⟨hp.1,hp.2,hs.mp h.2.2⟩⟩
  · have hn : ¬(raw.decode.Valid ∧ ThreeCNF raw.decode.formula ∧ raw.decode.Sat) := by
      rintro ⟨hv,ht,_⟩
      apply hg
      simp only [(validate_correct raw).mpr hv,(checkThree_correct raw.formula).mpr ht,Bool.true_and]
    exact iff_of_false fixedNo_not_mem hn

/-- Genuine total bitstring many-one correctness, with all malformed inputs and
semantic catalog violations mapped to one fixed positive no-instance. -/
theorem reduceThree_correct (bits : List Bool) :
    PositiveSubsetSumLanguage (reduceThree bits).1 ↔ ThreeCNFLanguage bits := by
  unfold reduceThree
  cases hp : (NPCNF.Encoding.parse bits).1 with
  | none => simp [hp,ThreeCNFLanguage,fixedNo_not_mem]
  | some raw => simp only [hp,reduceRaw_correct,ThreeCNFLanguage,Option.some.injEq]
                simp

end BalancedAssortments.NPSATSubsetSum
