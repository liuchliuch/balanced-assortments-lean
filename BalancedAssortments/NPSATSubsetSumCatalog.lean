import BalancedAssortments.NPSATSubsetSumCorrect
import BalancedAssortments.NPCNFBasic
import BalancedAssortments.ComplexityReduction

namespace BalancedAssortments.NPSATSubsetSum
open NPCNF

def catalogIndex (catalog : List ℕ) (v : ℕ) (hv : v ∈ catalog) : Fin catalog.length :=
  ⟨catalog.idxOf v,List.idxOf_lt_length_iff.mpr hv⟩

@[simp] lemma catalogIndex_get (catalog : List ℕ) (v : ℕ) (hv : v ∈ catalog) :
    catalog[(catalogIndex catalog v hv).val] = v := List.getElem_idxOf _

def indexedClause (catalog : List ℕ) (c : Clause) (hc : ∀ l ∈ c,l.var ∈ catalog) :
    List (IndexedLiteral catalog.length) :=
  c.attach.map (fun l => (catalogIndex catalog l.val.var (hc l.val l.property),l.val.positive))

@[simp] lemma indexedClause_length (catalog : List ℕ) (c : Clause) (hc : ∀ l ∈ c,l.var ∈ catalog) :
    (indexedClause catalog c hc).length = c.length := by simp [indexedClause]

lemma indexedClause_mem (catalog : List ℕ) (c : Clause) (hc : ∀ l ∈ c,l.var ∈ catalog)
    (x : IndexedLiteral catalog.length) : x ∈ indexedClause catalog c hc ↔
      ∃ l : {l // l ∈ c},x=(catalogIndex catalog l.val.var (hc l.val l.property),l.val.positive) := by
  simp [indexedClause,eq_comm]

def indexedFormula (input : Catalogued) (h : input.Valid) :
    IndexedFormula input.catalog.length input.formula.length := fun j =>
  indexedClause input.catalog input.formula[j.val] (h.2 _ (List.getElem_mem j.isLt))

lemma indexedFormula_three (input : Catalogued) (h : input.Valid) (h3 : ThreeCNF input.formula) :
    ∀ j,(indexedFormula input h j).length≤3 := by
  intro j
  rw [indexedFormula,indexedClause_length]
  exact h3 _ (List.getElem_mem j.isLt)

lemma literalEval_eq_true (assignment : Assignment) (l : Literal) :
    literalEval assignment l=true ↔ assignment l.var=l.positive := by
  cases l with | mk v p => cases p <;> simp [literalEval]

/-- Indexing uses the actual catalog length, irrespective of sparse label magnitude. -/
theorem catalog_sat_iff_indexed (input : Catalogued) (h : input.Valid) :
    input.Sat ↔ IndexedSat (indexedFormula input h) := by
  constructor
  · rintro ⟨assignment,hsat⟩
    refine ⟨fun i => assignment input.catalog[i.val],?_⟩
    intro j
    have hc := (formulaEval_eq_true_iff assignment input.formula).mp hsat _ (List.getElem_mem j.isLt)
    obtain ⟨l,hl,ht⟩ := (clauseEval_eq_true_iff assignment _).mp hc
    let x : IndexedLiteral input.catalog.length :=
      (catalogIndex input.catalog l.var (h.2 _ (List.getElem_mem j.isLt) l hl),l.positive)
    refine ⟨x,(indexedClause_mem _ _ _ x).mpr ⟨⟨l,hl⟩,rfl⟩,?_⟩
    simpa only [x,catalogIndex_get] using (literalEval_eq_true assignment l).mp ht
  · rintro ⟨assignment,hsat⟩
    let extended : Assignment := fun v => if hv : v ∈ input.catalog then assignment (catalogIndex input.catalog v hv) else false
    refine ⟨extended,(formulaEval_eq_true_iff extended input.formula).mpr ?_⟩
    intro c hc
    obtain ⟨j,hj⟩ := List.mem_iff_getElem.mp hc
    have hs := hsat ⟨j,hj.1⟩
    obtain ⟨x,hx,he⟩ := hs
    obtain ⟨l,rfl⟩ := (indexedClause_mem _ _ _ x).mp hx
    apply (clauseEval_eq_true_iff extended c).mpr
    refine ⟨l.val,?_,(literalEval_eq_true extended l.val).mpr ?_⟩
    · simpa only [hj.2] using l.property
    · have hm := h.2 _ (List.getElem_mem hj.1) l.val l.property
      simpa [extended,hm] using he

theorem catalog_sat_iff_subset_sum (input : Catalogued) (h : input.Valid) (h3 : ThreeCNF input.formula) :
    input.Sat ↔ ComplexityReduction.SubsetSum Finset.univ (itemValue (indexedFormula input h))
      (targetValue input.catalog.length input.formula.length) := by
  rw [catalog_sat_iff_indexed input h,indexed_sat_iff_subset_sum _ (indexedFormula_three input h h3)]
  simp [ComplexityReduction.SubsetSum]

end BalancedAssortments.NPSATSubsetSum
