import BalancedAssortments.NPCNFStackValidateCalls

namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary
open Encoding

def literalCost (l : BitLiteral) (labels : List (List Bool)) : ℕ :=
  6*l.labelBits.length+NPStackCatalogueMember.memberCost l.labelBits labels+19

def clauseCost (clause : BitClause) (labels : List (List Bool)) : ℕ :=
  (clause.map (fun l => literalCost l labels)).sum+5

def formulaCost (formula : BitFormula) (labels : List (List Bool)) : ℕ :=
  (formula.map (fun c => 11+clauseCost c labels)).sum+12

def Members (formula : BitFormula) (labels : List (List Bool)) : Prop :=
  ∀ c∈formula,∀ l∈c,value l.labelBits∈labels.map value

lemma literal_run (l : BitLiteral) (labels : List (List Bool)) (rest o f : List Bool)
    (hm : value l.labelBits∈labels.map value) :
    Run program (literalCost l labels)
      (cfg .readSign (store (tagBits [l.positive]++false::(tagBits l.labelBits++false::rest)) o f (dataFields labels) [] [] []))
      (cfg .readSign (store rest o f (dataFields labels) [] [] [])) := by
  have hmem := member_call l.labelBits rest o f labels
  simp only [hm,decide_true] at hmem
  have hh := (sign_call l.positive (tagBits l.labelBits++false::rest) o f (dataFields labels)).trans
    ((literal_read_call l.labelBits rest o f (dataFields labels)).trans (hmem.trans
      (.succ (member_check true l.labelBits rest o f (dataFields labels))
        (clear_query_call l.labelBits rest o f (dataFields labels)))))
  convert hh using 1 <;> unfold literalCost <;> omega

lemma clause_run (clause : BitClause) (labels : List (List Bool)) (rest o f : List Bool)
    (hm : ∀ l∈clause,value l.labelBits∈labels.map value) :
    Run program (clauseCost clause labels)
      (cfg .readSign (store (dataFields (clauseFields clause)++rest) o f (dataFields labels) [] [] []))
      (cfg .readHeader (store rest o f (dataFields labels) [] [] [])) := by
  induction clause with
  | nil => simpa [clauseCost,clauseFields,dataFields] using clause_end_call rest o f (dataFields labels)
  | cons l ls ih =>
    have hh := (literal_run l labels (dataFields (clauseFields ls)++rest) o f (hm l (by simp))).trans
      (ih (fun x hx => hm x (by simp [hx])))
    convert hh using 1 <;> simp [clauseCost,clauseFields,dataFields,List.append_assoc] <;> omega

lemma formula_run (formula : BitFormula) (labels : List (List Bool)) (o f : List Bool)
    (hm : Members formula labels) :
    Run program (formulaCost formula labels)
      (cfg .readHeader (store (dataFields (formulaFields formula)) o f (dataFields labels) [] [] []))
      (cfg .accept (store [] o f (dataFields labels) [] [] [])) := by
  induction formula with
  | nil =>
    have hh := (header_call false [] o f (dataFields labels)).trans (.one (check_end_empty o f (dataFields labels)))
    simpa [formulaCost,formulaFields,dataFields] using hh
  | cons c cs ih =>
    have hclause := clause_run c labels (dataFields (formulaFields cs)) o f (hm c (by simp))
    have hrest := ih (fun d hd => hm d (by simp [hd]))
    have hh := (header_call true (dataFields (clauseFields c)++dataFields (formulaFields cs)) o f (dataFields labels)).trans
      (hclause.trans hrest)
    convert hh using 1 <;> simp [formulaCost,formulaFields,dataFields,List.flatMap_append,List.append_assoc] <;> omega

lemma validation_run (formula : BitFormula) (labels : List (List Bool)) (f : List Bool)
    (hm : Members formula labels) :
    Run program (5*(dataFields (formulaFields formula)).length+4+formulaCost formula labels)
      (cfg .saveFormula (store (dataFields (formulaFields formula)) [] f (dataFields labels) [] [] []))
      (cfg .accept (store [] (dataFields (formulaFields formula)) f (dataFields labels) [] [] [])) :=
  (save_formula_call (dataFields (formulaFields formula)) f (dataFields labels)).trans
    (formula_run formula labels (dataFields (formulaFields formula)) f hm)

def freshBits (labels : List (List Bool)) : List Bool := (addCarry (StackCatalogue.selectedMaximum labels []) [] true).1

lemma header_run (labels : List (List Bool)) (rest : List Bool) (hn : (labels.map value).Nodup) :
    Run program (StackCatalogue.catalogueCost labels [] []+1)
      ⟨.header (.outer (.main .readTag)),store (dataFields (catalogFields labels)++rest) [] [] [] [] [] []⟩
      (cfg .saveFormula (store rest [] (freshBits labels) (dataFields labels.reverse) [] [] [])) := by
  have hsource := StackCatalogue.catalogue_run labels [] rest [] (by simpa using hn)
  simp only [List.append_nil,dataFields,List.flatMap_nil] at hsource
  have h := hsource.relocate_exact headerMap State.header headerMap_injective header_extends
    (c' := ⟨.header (.outer (.main .readTag)),store (dataFields (catalogFields labels)++rest) [] [] [] [] [] []⟩)
    (d' := ⟨.header (.outer (.main .accept)),store rest [] (freshBits labels) (dataFields labels.reverse) [] [] []⟩)
    ⟨rfl,by
      intro k;cases k with
      | inl r => cases r <;> rfl
      | inr r => cases r <;> rfl⟩
    ⟨rfl,by
      intro k;cases k with
      | inl r => cases r <;> rfl
      | inr r => cases r <;> rfl⟩
    (by
      intro k hk
      cases k with
      | inl r => exact (hk (.inl r) rfl).elim
      | inr r => cases r with
        | original => rfl
        | input => exact (hk (.inr .input) rfl).elim
        | tag => exact (hk (.inr .tag) rfl).elim
        | maximum => exact (hk (.inr .maximum) rfl).elim
        | fresh => exact (hk (.inr .fresh) rfl).elim)
  have hreturn : Step program ⟨.header (.outer (.main .accept)),store rest [] (freshBits labels) (dataFields labels.reverse) [] [] []⟩
      (cfg .saveFormula (store rest [] (freshBits labels) (dataFields labels.reverse) [] [] [])) := by
    simp [Step,successors,program,code,cfg]
  exact h.trans (.one hreturn)

def preparationCost (raw : Raw) : ℕ := StackCatalogue.catalogueCost raw.catalog [] []+1+
  (5*(dataFields (formulaFields raw.formula)).length+4+formulaCost raw.formula raw.catalog.reverse)

/-- Concrete catalogue parsing, semantic nodup checks, fresh-label arithmetic,
formula skeleton validation and membership checks, with exact retained output. -/
theorem prepare_run (raw : Raw) (h : raw.decode.Valid) :
    Run program (preparationCost raw)
      ⟨.header (.outer (.main .readTag)),store (dataFields (fields raw)) [] [] [] [] [] []⟩
      (cfg .accept (store [] (dataFields (formulaFields raw.formula)) (freshBits raw.catalog)
        (dataFields raw.catalog.reverse) [] [] [])) := by
  have hn : (raw.catalog.map value).Nodup := h.1
  have hmembers : Members raw.formula raw.catalog.reverse := by
    intro c hc l hl
    have hh := h.2 (c.map BitLiteral.decode) (List.mem_map.mpr ⟨c,hc,rfl⟩)
      l.decode (List.mem_map.mpr ⟨l,hl,rfl⟩)
    simpa [Raw.decode,BitLiteral.decode,List.map_reverse] using hh
  have hhead := header_run raw.catalog (dataFields (formulaFields raw.formula)) hn
  have hh := hhead.trans (validation_run raw.formula raw.catalog.reverse (freshBits raw.catalog) hmembers)
  simpa [preparationCost,fields,dataFields,List.flatMap_append] using hh

lemma freshBits_value (labels : List (List Bool)) : value (freshBits labels)=maxLabel (labels.map value)+1 :=
  StackCatalogue.fresh_value labels

end BalancedAssortments.NPCNF.StackValidate
