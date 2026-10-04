import BalancedAssortments.ComplexitySourceReindex
import BalancedAssortments.ComplexityTimeTotalCertificates
import BalancedAssortments.ComplexityReal
import BalancedAssortments.NPSATSubsetSumLists

/-! The actual signed-field source schema for the Subset Sum reduction. This
module is semantic; finite-stack construction is refined to this record. -/
namespace BalancedAssortments.ComplexitySourceModel
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline ComplexityTimeSourceParsing

def natFraction (num den : ℕ) : Fraction := ⟨(num.bits,[]),den.bits⟩

@[simp] lemma natFraction_decode (num den : ℕ) : decode (natFraction num den)=(num:ℚ)/(den:ℚ) := by
  simp [natFraction,decode,zvalue]
@[simp] lemma natFraction_valid (num den : ℕ) : Valid (natFraction num den) ↔ 0<den := by
  simp [natFraction,Valid]

def anchor (B : ℕ) : Fraction × Fraction := (natFraction (5*B) 1,natFraction 1 1)
def item (B a : ℕ) : Fraction × Fraction := (natFraction (3*B+a) 1,natFraction B a)

def model (B : ℕ) (items : List ℕ) : Source where
  declaredCount := (items.length+1).bits
  capacity := (2:ℕ).bits
  alpha := natFraction 1 1
  target := natFraction (3*B) 1
  products := anchor B::items.map (item B)

lemma model_length (B : ℕ) (items : List ℕ) : (model B items).products.length=items.length+1 := by
  simp [model]

lemma model_legal (B : ℕ) (items : List ℕ) (hB : 0<B)
    (hi : ∀ a ∈ items,0<a) (hne : items≠[]) : LegalSource (model B items) := by
  have hn : 0 < items.length := List.length_pos.mpr hne
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [model]
  · simpa [model] using Nat.zero_lt_succ items.length
  · simp [model]
  · simp only [model,value_bits,List.length_cons,List.length_map];omega
  · simp [model]
  · simp [model]
  · simp [model]
  · intro rv hr
    simp only [model,List.mem_cons,List.mem_map] at hr
    rcases hr with rfl | ⟨a,ha,rfl⟩
    · simp only [anchor,natFraction_valid,natFraction_decode,div_one]
      norm_num
      positivity
    · have hap := hi a ha
      simp only [item,natFraction_valid,natFraction_decode,div_one]
      refine ⟨⟨by decide,by positivity⟩,⟨hap,div_pos (by positivity) (by positivity)⟩⟩

def modelEquiv (B : ℕ) (items : List ℕ) : Fin (model B items).products.length ≃ Option (Fin items.length) :=
  (finCongr (model_length B items)).trans (finSuccEquiv items.length)

lemma model_values_none (B : ℕ) (items : List ℕ) :
    decodedValues (model B items).attractions ((modelEquiv B items).symm none)=1 ∧
    decodedValues (model B items).prices ((modelEquiv B items).symm none)=5*B := by
  simp [decodedValues,modelEquiv,Source.attractions,Source.prices,
    model,anchor,lookup_value,List.getD,natFraction_decode]

lemma model_values_some (B : ℕ) (items : List ℕ) (i : Fin items.length) :
    decodedValues (model B items).attractions ((modelEquiv B items).symm (some i))=(B:ℚ)/items[i.val] ∧
    decodedValues (model B items).prices ((modelEquiv B items).symm (some i))=3*B+items[i.val] := by
  simp [decodedValues,modelEquiv,Source.attractions,Source.prices,
    model,anchor,item,lookup_value,List.getD,natFraction_decode,i.isLt]

lemma list_subsetSum_iff (items : List ℕ) (B : ℕ) :
    NPSATSubsetSum.ListSubsetSum items B ↔
      ComplexityReal.SubsetSum Finset.univ (fun i : Fin items.length => items[i.val]) B := by
  have h := NPSATSubsetSum.enumerated_subset_sum_iff (List.finRange items.length)
    (List.nodup_finRange _) (fun i => List.mem_finRange i) (fun i => items[i.val]) B
  have hl : (List.finRange items.length).map (fun i => items[i.val])=items := by
    rw [← List.ofFn_eq_map,List.ofFn_getElem]
  rw [hl] at h
  simpa [ComplexityReal.SubsetSum] using h

lemma model_values_reindex (B : ℕ) (items : List ℕ) :
    ((fun j : Fin (model B items).products.length => (decodedValues (model B items).attractions j : ℝ)) ∘
      (modelEquiv B items).symm)=ComplexityReal.attractiveness (fun i : Fin items.length => items[i.val]) B ∧
    ((fun j : Fin (model B items).products.length => (decodedValues (model B items).prices j : ℝ)) ∘
      (modelEquiv B items).symm)=ComplexityReal.price (fun i : Fin items.length => items[i.val]) B := by
  constructor <;> funext j <;> cases j with
  | none =>
    have hh := model_values_none B items
    simp only [Function.comp_apply,hh.1,hh.2,ComplexityReal.attractiveness,ComplexityReal.price]
    push_cast
    rfl
  | some i =>
    have hh := model_values_some B items i
    simp only [Function.comp_apply,hh.1,hh.2,ComplexityReal.attractiveness,ComplexityReal.price]
    push_cast
    rfl

/-- The source record is in exactly the schema accepted by the total BMS
verifier, and its actual real decision problem is the Subset Sum instance. -/
theorem model_correct (B : ℕ) (items : List ℕ) (hB : 0<B)
    (hi : ∀ a ∈ items,0<a) :
    SourceYes (model B items) ↔ NPSATSubsetSum.ListSubsetSum items B := by
  have hreindex := Sales.decision_reindex (modelEquiv B items).symm
    (fun j => (decodedValues (model B items).attractions j : ℝ))
    (fun j => (decodedValues (model B items).prices j : ℝ)) 1 (3*(B:ℝ)) 2
  rw [(model_values_reindex B items).1,(model_values_reindex B items).2] at hreindex
  have hsource : SourceYes (model B items) ↔
      ∃ w : Option (Fin items.length) → ℝ,
        Sales.CompactFeasible (ComplexityReal.attractiveness (fun i => items[i.val]) B) w 2 ∧
        Sales.Balanced 1 w ∧ 3*(B:ℝ)≤Sales.objective (ComplexityReal.price (fun i => items[i.val]) B) w := by
    simpa only [SourceYes,model,natFraction_decode,div_one,value_bits,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using hreindex.symm
  rw [hsource,list_subsetSum_iff,ComplexityReal.compact_reduction_iff _ _ hB
    (fun i => hi _ (List.getElem_mem i.isLt))]
  exact exists_congr (fun w => (ComplexityReal.compactDecision_iff_sales _ _ w).symm)

end BalancedAssortments.ComplexitySourceModel
