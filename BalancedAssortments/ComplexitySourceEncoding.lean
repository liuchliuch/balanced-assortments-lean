import BalancedAssortments.ComplexitySourceModel

namespace BalancedAssortments.ComplexitySourceModel
open ComplexityTimeSourceParsing ComplexityEncoding ComplexityTimeBinary

/-- Positive-rational source parameters encoded in the full signed verifier schema. -/
def itemNatFields (B a : ℕ) : List ℕ := [3*B+a,0,1,B,0,a]
def sourceNatFields (B : ℕ) (items : List ℕ) : List ℕ :=
  [items.length+1,2,1,0,1,3*B,0,1,5*B,0,1,1,0,1]++items.flatMap (itemNatFields B)

def sourceEncoding (B : ℕ) (items : List ℕ) : List Bool := encodeFields (sourceNatFields B items)

lemma parseProducts_items (B : ℕ) (items : List ℕ) :
    (parseProducts ((items.flatMap (itemNatFields B)).map Nat.bits)).1=some (items.map (item B)) := by
  induction items with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons,List.map_append,itemNatFields,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,parseProducts,ih,Option.map_some,List.map_cons]
    simp [item,natFraction]

lemma sourceEncoding_parses (B : ℕ) (items : List ℕ) :
    (parseSource (sourceEncoding B items)).1=some (model B items) := by
  simp only [sourceEncoding,parseSource,(EncodingTime.parse_encoded _).1]
  simp only [sourceNatFields,List.map_append,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    packSource,parseProducts,parseProducts_items,Option.map_some]
  simp [model,anchor,natFraction]

lemma sourceEncoding_language (B : ℕ) (items : List ℕ) (hB : 0<B)
    (hi : ∀ a ∈ items,0<a) (hne : items≠[]) :
    SourceLanguage (sourceEncoding B items) ↔ NPSATSubsetSum.ListSubsetSum items B := by
  constructor
  · rintro ⟨s,hs,_,hyes⟩
    rw [sourceEncoding_parses] at hs
    cases Option.some.inj hs
    exact (model_correct B items hB hi).mp hyes
  · intro hsum
    exact ⟨model B items,sourceEncoding_parses B items,model_legal B items hB hi hne,
      (model_correct B items hB hi).mpr hsum⟩

def fixedNoSource : List Bool := sourceEncoding 1 [2]

lemma fixedNoSource_legal : LegalSource (model 1 [2]) := model_legal 1 [2] (by decide) (by simp) (by simp)
lemma fixedNoSource_not_mem : ¬ SourceLanguage fixedNoSource := by
  rw [fixedNoSource,sourceEncoding_language 1 [2] (by decide) (by simp) (by simp)]
  rintro ⟨xs,hxs,hs⟩
  rcases List.sublist_singleton.mp hxs with rfl | rfl <;> simp at hs

lemma listSubsetSum_reverse (items : List ℕ) (B : ℕ) :
    NPSATSubsetSum.ListSubsetSum items.reverse B ↔ NPSATSubsetSum.ListSubsetSum items B := by
  constructor
  · rintro ⟨xs,hxs,hs⟩
    exact ⟨xs.reverse,by simpa using hxs.reverse,by simpa using hs⟩
  · rintro ⟨xs,hxs,hs⟩
    exact ⟨xs.reverse,hxs.reverse,by simpa using hs⟩

/-- The streaming finite constructor prepends item records, hence their reverse
order; coordinate permutation does not change the source decision language. -/
theorem reversed_sourceEncoding_language (B : ℕ) (items : List ℕ) (hB : 0<B)
    (hi : ∀ a ∈ items,0<a) (hne : items≠[]) :
    SourceLanguage (sourceEncoding B items.reverse) ↔ NPSATSubsetSum.ListSubsetSum items B := by
  rw [sourceEncoding_language B items.reverse hB (by simpa using hi) (by simpa using hne),listSubsetSum_reverse]

end BalancedAssortments.ComplexitySourceModel
