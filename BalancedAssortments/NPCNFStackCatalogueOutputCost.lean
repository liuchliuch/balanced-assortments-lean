import BalancedAssortments.NPCNFStackCatalogueOutput
import BalancedAssortments.NPStackFieldsRun

namespace BalancedAssortments.NPCNF.StackCatalogueOutput
open NPStack NPStack.Macros NPStackFields Encoding

lemma recordsCost_eq (labels : List (List Bool)) :
    recordsCost labels=10*(labels.map List.length).sum+14*labels.length+1 := by
  induction labels with
  | nil => rfl
  | cons l ls ih => simp only [recordsCost,List.map_cons,List.sum_cons,List.length_cons] at *;omega

lemma catalogue_cost_bound (original allocated : List (List Bool)) :
    recordsCost original+recordsCost allocated+3 ≤
      14*((dataFields original).length+(dataFields allocated).length)+5 := by
  rw [recordsCost_eq,recordsCost_eq,dataFields_length,dataFields_length]
  omega

lemma catalogueBody_length (labels : List (List Bool)) :
    (dataFields (catalogueBody labels)).length=2*(labels.map List.length).sum+4*labels.length := by
  induction labels with
  | nil => rfl
  | cons l ls ih =>
    simp only [catalogueBody,List.flatMap_cons,dataFields,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.length_append,List.length_cons,List.length_nil,
      List.map_cons,List.sum_cons,tagBits_length] at *
    simp only [tagBits,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil] at *
    omega

lemma output_length_bound (original allocated : List (List Bool)) (formula : List Bool) :
    (dataFields (catalogFields (original.reverse++allocated.reverse))++formula).length ≤
      4*((dataFields original).length+(dataFields allocated).length)+3+formula.length := by
  rw [catalogFields_body]
  simp only [dataFields,List.flatMap_append,List.length_append]
  change (dataFields (catalogueBody (original.reverse++allocated.reverse))).length+3+formula.length≤_
  rw [catalogueBody_length]
  simp only [List.map_append,List.map_reverse,List.sum_append,List.sum_reverse,List.length_append,List.length_reverse]
  change _≤4*((dataFields original).length+(dataFields allocated).length)+3+formula.length
  rw [dataFields_length,dataFields_length]
  omega

theorem catalogue_halted_correct (original allocated : List (List Bool)) (formula : List Bool)
    {t : ℕ} {c : Config Register (Label State)} {accepted : Bool}
    (hr : Run program t (cfg .marker0 (store (dataFields original) (dataFields allocated) formula)) c)
    (hc : program.code c.pc=.halt accepted) :
    t=recordsCost original+recordsCost allocated+3 ∧
      c=cfg .accept (store [] [] (dataFields (catalogFields (original.reverse++allocated.reverse))++formula)) := by
  exact hr.halted_unique (noChoice_deterministic (compile_noChoice macroCode .marker0 .original .output))
    (catalogue_run original allocated formula) hc rfl

end BalancedAssortments.NPCNF.StackCatalogueOutput
