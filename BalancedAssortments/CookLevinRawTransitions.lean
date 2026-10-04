import BalancedAssortments.CookLevinRawSteps

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

def encodeRule {q g : ℕ} (r : Rule q g) : RawRule :=
  ⟨r.source.val.bits,r.target.val.bits,r.read.val.bits,r.write.val.bits,r.move⟩
lemma encodeRule_valid {M : Machine} (r : Rule M.stateExtra M.symbolExtra) : RuleEncoding (encodeRule r) r := by
  constructor <;> simp [encodeRule]

def ruleAt (M : Machine) (i : Fin (M.rules.length+1)) : Option RawRule :=
  Fin.cases none (fun j => some (encodeRule M.rules[j.val])) i

lemma machineChoices_zip (M : Machine) :
    (machineConstants M).choices.zip (none::(machineConstants M).rules.map some)=
      (List.finRange (M.rules.length+1)).map (fun i => (i.val.bits,ruleAt M i)) := by
  have hc : (machineConstants M).choices=(List.finRange (M.rules.length+1)).map (fun i => i.val.bits) := by
    simpa only [machineConstants,List.map_map,Function.comp_def] using
      (congrArg (List.map Nat.bits) (List.map_coe_finRange (M.rules.length+1))).symm
  have hr : none::(machineConstants M).rules.map some=(List.finRange (M.rules.length+1)).map (ruleAt M) := by
    rw [List.finRange_succ]
    simp only [List.map_cons,List.map_map,ruleAt,Fin.cases_zero,Fin.cases_succ,Function.comp_def]
    congr 1
    change (M.rules.map encodeRule).map some=_
    simpa only [List.map_map,Function.comp_def] using
      (congrArg (List.map (fun r => some (encodeRule r))) (List.finRange_map_getElem M.rules)).symm
  rw [hc,hr,List.zip_map']

lemma machineConstants_ranges (M : Machine) :
    (machineConstants M).states.map value=List.range (M.stateExtra+1) ∧
    (machineConstants M).symbols.map value=List.range (M.symbolExtra+3) ∧
    (machineConstants M).choices.map value=List.range (M.rules.length+1) ∧
    (machineConstants M).accepting.map value=((List.finRange (M.stateExtra+1)).filter M.accepting).map Fin.val := by
  simp [machineConstants,List.map_map,Function.comp_def]

lemma rawTransitions_refines (M : Machine) {W T : ℕ} {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) d)
    (steps cells : List (List Bool)) (ht : steps.map value=List.range T) (hp : cells.map value=List.range W) :
    decodeFormula (rawTransitions d steps (machineConstants M).states cells (machineConstants M).symbols
      (machineConstants M).accepting (machineConstants M).choices (machineConstants M).rules).1=
      transitionFormula M W T := by
  unfold rawTransitions transitionFormula
  apply rangeFlatMap_refine steps ht
  intro old hold t ho
  have hn : value (addCarry old [] true).1=t.val+1 := by simp [addCarry_value,ho,value]
  simp only [machineChoices_zip,rawFlatMap_decode,List.flatMap_map,allFin]
  apply congrArg (List.flatMap · (List.finRange (M.rules.length+1)))
  funext i
  rw [rawGuardComputed_decode,choiceLabel_refines hd t i ho (value_bits i.val)]
  change guardLiteral (pos (Var.choice t i : TVar M W T)) _ = _
  apply congrArg (guardLiteral (pos (Var.choice t i : TVar M W T)))
  refine Fin.cases ?_ (fun j => ?_) i
  · exact rawHaltBody_refines M hd t ho hn _ cells _ _ (machineConstants_ranges M).1 hp
      (machineConstants_ranges M).2.1 (machineConstants_ranges M).2.2.2
  · exact rawRuleBody_refines M hd t ho hn cells _ hp (machineConstants_ranges M).2.1
      (encodeRule M.rules[j.val]) M.rules[j.val] (encodeRule_valid _)

end BalancedAssortments.CookLevin
