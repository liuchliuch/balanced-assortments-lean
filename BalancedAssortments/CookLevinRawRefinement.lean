import BalancedAssortments.CookLevinRawConstructor

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitLiteral BitClause BitFormula bitPositive bitNegative)

def decodeFormula (F : BitFormula) : Formula := F.map (List.map BitLiteral.decode)
@[simp] lemma decodeFormula_append (F G : BitFormula) : decodeFormula (F++G)=decodeFormula F++decodeFormula G := by simp [decodeFormula]
@[simp] lemma rawAppend_decode (F G : BitFormula × ℕ) :
    decodeFormula (rawAppend F G).1=decodeFormula F.1++decodeFormula G.1 := by simp [rawAppend]
@[simp] lemma rawForce_decode (label : List Bool × ℕ) :
    decodeFormula (rawForce label).1=[[positive (value label.1)]] := rfl
@[simp] lemma rawCopy_decode (old next : List Bool × ℕ) :
    decodeFormula (rawCopy old next).1=[[negative (value old.1),positive (value next.1)]] := rfl
@[simp] lemma rawSingle_decode (labels : List (List Bool) × ℕ) :
    decodeFormula (rawSingle labels).1=[labels.1.map (fun x => positive (value x))] := by
  simp [rawSingle,decodeFormula,rawMap_eq,List.map_map,Function.comp_def]
@[simp] lemma rawGuardComputed_decode (sign : Bool) (label : List Bool × ℕ) (body : BitFormula × ℕ) :
    decodeFormula (rawGuardComputed sign label body).1=
      guardLiteral ⟨value label.1,sign⟩ (decodeFormula body.1) := rawGuard_decode _ _
lemma rawFlatMap_decode {α : Type*} (f : α → BitFormula × ℕ) (xs : List α) :
    decodeFormula (rawFlatMap f xs).1=xs.flatMap (fun x => decodeFormula (f x).1) := by
  simp [decodeFormula,rawFlatMap_eq,List.map_flatMap]

lemma stateLabel_value (d : RawDimensions) (t s : List Bool) :
    value (stateLabel d t s).1=value s+value d.q*value t := by
  simp [stateLabel,BitExpr.run_correct,stateIndexExpr_meaning,RawDimensions.inputs]
lemma headLabel_value (d : RawDimensions) (t p : List Bool) :
    value (headLabel d t p).1=(value d.t+1)*value d.q+(value p+value d.w*value t) := by
  simp [headLabel,BitExpr.run_correct,headIndexExpr_meaning,RawDimensions.inputs]
lemma tapeLabel_value (d : RawDimensions) (t p a : List Bool) :
    value (tapeLabel d t p a).1=((value d.t+1)*value d.q+(value d.t+1)*value d.w)+
      (value a+value d.g*value p+(value d.w*value d.g)*value t) := by
  simp [tapeLabel,BitExpr.run_correct,tapeIndexExpr_meaning,RawDimensions.inputs]
lemma choiceLabel_value (d : RawDimensions) (t r : List Bool) :
    value (choiceLabel d t r).1=((value d.t+1)*value d.q+(value d.t+1)*value d.w)+
      ((value d.t+1)*(value d.w*value d.g)+(value r+value d.r*value t)) := by
  simp [choiceLabel,BitExpr.run_correct,choiceIndexExpr_meaning,RawDimensions.inputs]

lemma exactlyOneLabels_finRange {q g W T R n : ℕ} (f : Fin n → Var q g W T R)
    (hf : Function.Injective f) :
    exactlyOneLabels ((List.finRange n).map (fun i => index (f i)))=exactlyOne f := by
  have hi : Function.Injective (fun i => index (f i)) := index_injective.comp hf
  simp [exactlyOneLabels,exactlyOne,allFin,List.flatMap_map,List.map_map,Function.comp_def,hi.eq_iff,pos,neg]

/-- List-level dependent refinement for a range represented by arbitrary padded
bit strings. Only the proof decodes the range; the raw loops consume the list. -/
lemma rangeMap_refine {α : Type*} {n : ℕ} (xs : List (List Bool))
    (hx : xs.map value=List.range n) (raw : List Bool → α) (spec : Fin n → α)
    (h : ∀ x∈xs,∀ i : Fin n,value x=i.val → raw x=spec i) :
    xs.map raw=(List.finRange n).map spec := by
  have hv : ∀ x∈xs,value x<n := by
    intro x hx'
    exact List.mem_range.mp (hx ▸ List.mem_map.mpr ⟨x,hx',rfl⟩)
  let cast (k : ℕ) : α := if hk : k<n then spec ⟨k,hk⟩ else (List.finRange n).map spec |>.headD (raw [])
  have hr : xs.map raw=(xs.map value).map cast := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx'
    have hb := hv x hx'
    simpa only [Function.comp_apply,cast,dif_pos hb] using h x hx' ⟨value x,hb⟩ rfl
  rw [hr,hx]
  have he : List.range n=(List.finRange n).map Fin.val := by simp
  rw [he,List.map_map]
  apply List.map_congr_left
  intro i hi
  simp [cast,i.isLt]

lemma rawMoveMatch_correct (m : Move) (old next : List Bool) :
    (rawMoveMatch m old next).1=true ↔ (value next : ℤ)=(value old : ℤ)+m.displacement := by
  cases m <;> simp [rawMoveMatch,Encoding.compare_eq_iff,addCarry_value,value,Move.displacement] <;> omega

lemma rawWindowFuel_length (word : List Bool) (clock : List Unit) :
    (rawWindowFuel word clock).1.length=windowWidth word clock.length := by
  simp [rawWindowFuel,rawMap_eq,windowWidth]; omega

lemma rawInputCells_length (word : List Bool) (clock : List Unit) :
    (rawInputCells word clock).1.length=windowWidth word clock.length := by
  simp [rawInputCells,rawMap_eq,windowWidth]; omega

lemma rawInputCells_decode (word : List Bool) (clock : List Unit) :
    (rawInputCells word clock).1.map value=
      List.replicate clock.length 2 ++ word.map Bool.toNat ++ List.replicate clock.length 2 ++ [2] := by
  simp only [rawInputCells,rawMap_eq,List.map_append,List.map_map,List.map_cons,List.map_nil]
  have hc : clock.map (fun _ => value [false,true])=List.replicate clock.length 2 := by simp [value]
  simp only [Function.comp_def]
  rw [hc]
  norm_num [value]

end BalancedAssortments.CookLevin
