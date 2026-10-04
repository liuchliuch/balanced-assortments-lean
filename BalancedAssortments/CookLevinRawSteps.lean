import BalancedAssortments.CookLevinRawShape

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitFormula)

lemma listMap_refine {α : Type*} {n : ℕ} (xs : List (List Bool)) (indices : List (Fin n))
    (hx : xs.map value=indices.map Fin.val) (raw : List Bool → α) (spec : Fin n → α)
    (h : ∀ x∈xs,∀ i : Fin n,value x=i.val → raw x=spec i) :
    xs.map raw=indices.map spec := by
  have hv : ∀ x∈xs,value x<n := by
    intro x hx'
    have hh : value x∈indices.map Fin.val := hx ▸ List.mem_map.mpr ⟨x,hx',rfl⟩
    obtain ⟨i,_,he⟩ := List.mem_map.mp hh
    exact he ▸ i.isLt
  let cast (k : ℕ) : α := if hk : k<n then spec ⟨k,hk⟩ else raw []
  have hr : xs.map raw=(xs.map value).map cast := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx'
    have hb := hv x hx'
    simpa only [Function.comp_apply,cast,dif_pos hb] using h x hx' ⟨value x,hb⟩ rfl
  rw [hr,hx,List.map_map]
  apply List.map_congr_left
  intro i hi
  simp [cast,i.isLt]

lemma rawAccept_refines (M : Machine) {W T : ℕ} {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) d)
    (t : Fin (T+1)) {bt : List Bool} (ht : value bt=t.val)
    (accepting : List (List Bool))
    (ha : accepting.map value=((List.finRange (M.stateExtra+1)).filter M.accepting).map Fin.val) :
    decodeFormula (rawAccept d bt accepting).1=acceptFormula M (W := W) t := by
  simp only [rawAccept,rawSingle_decode,rawMap_eq,List.map_map,acceptFormula]
  congr 1
  apply listMap_refine accepting _ ha
  intro bs hbs s hs
  change positive (value (stateLabel d bt bs).1)=pos (Var.state t s : TVar M W T)
  rw [stateLabel_refines hd t s ht hs]
  rfl

lemma rawHaltBody_refines (M : Machine) {W T : ℕ} {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) d)
    (t : Fin T) {old next : List Bool} (ho : value old=t.val) (hn : value next=t.val+1)
    (states cells symbols accepting : List (List Bool))
    (hs : states.map value=List.range (M.stateExtra+1)) (hp : cells.map value=List.range W)
    (ha : symbols.map value=List.range (M.symbolExtra+3))
    (hacc : accepting.map value=((List.finRange (M.stateExtra+1)).filter M.accepting).map Fin.val) :
    decodeFormula (rawHaltBody d old next states cells symbols accepting).1=haltBody M (W := W) t := by
  simp only [rawHaltBody,haltBody,rawAppend_decode]
  rw [rawAccept_refines M hd t.castSucc ho accepting hacc]
  apply congrArg (acceptFormula M (W := W) t.castSucc ++ ·)
  apply congrArg₂ List.append
  · apply rangeFlatMap_refine states hs
    intro bs hbs s hbsval
    simp only [rawCopy_decode,stateLabel_refines hd t.castSucc s ho hbsval,
      stateLabel_refines hd t.succ s hn hbsval]
    rfl
  · apply congrArg₂ List.append
    · apply rangeFlatMap_refine cells hp
      intro bp hbp p hbpval
      simp only [rawCopy_decode,headLabel_refines hd t.castSucc p ho hbpval,
        headLabel_refines hd t.succ p hn hbpval]
      rfl
    · apply rangeFlatMap_refine cells hp
      intro bp hbp p hbpval
      apply rangeFlatMap_refine symbols ha
      intro ba hba a hbaval
      simp only [rawCopy_decode,tapeLabel_refines hd t.castSucc p a ho hbpval hbaval,
        tapeLabel_refines hd t.succ p a hn hbpval hbaval]
      rfl

lemma rawHeadTarget_refines (M : Machine) {W T : ℕ} {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) d)
    (t : Fin T) (p : Fin W) {next old : List Bool} (hn : value next=t.val+1) (ho : value old=p.val)
    (m : Move) (cells : List (List Bool)) (hp : cells.map value=List.range W) :
    decodeFormula (rawHeadTarget d next old m cells).1=headTarget M t p m := by
  simp only [rawHeadTarget,rawSingle_decode,rawFlatMap_eq,List.map_flatMap,headTarget]
  have hm := rangeMap_refine cells hp
    (fun cell => ((if (rawMoveMatch m old cell).1 then [(headLabel d next cell).1] else []).map
      (fun x => positive (value x))))
    (fun k : Fin W => if (k.val : ℤ)=(p.val : ℤ)+m.displacement then [pos (Var.head t.succ k : TVar M W T)] else [])
    (by
      intro cell hcell k hk
      have hmove : (rawMoveMatch m old cell).1=true ↔ (k.val : ℤ)=(p.val : ℤ)+m.displacement := by
        simpa only [ho,hk] using rawMoveMatch_correct m old cell
      by_cases htest : (k.val : ℤ)=(p.val : ℤ)+m.displacement
      · simp only [(hmove.mpr htest),ite_true,List.map_cons,List.map_nil,if_pos htest,
          headLabel_refines hd t.succ k hn hk]
        rfl
      · have hh : (rawMoveMatch m old cell).1=false := Bool.eq_false_iff.mpr (fun he => htest (hmove.mp he))
        simp only [hh,Bool.false_eq_true,ite_false,List.map_nil,if_neg htest])
  congr 1
  have hf := congrArg List.flatten hm
  rw [← List.flatMap_def,← List.flatMap_def] at hf
  rw [hf]
  generalize List.finRange W=ks
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    by_cases hk : (k.val : ℤ)=(p.val : ℤ)+m.displacement <;> simp [hk,ih]

structure RuleEncoding {M : Machine} (raw : RawRule) (r : Rule M.stateExtra M.symbolExtra) : Prop where
  source_eq : value raw.source=r.source.val
  target_eq : value raw.target=r.target.val
  read_eq : value raw.read=r.read.val
  write_eq : value raw.write=r.write.val
  move_eq : raw.move=r.move

lemma rawRuleBody_refines (M : Machine) {W T : ℕ} {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) d)
    (t : Fin T) {old next : List Bool} (ho : value old=t.val) (hn : value next=t.val+1)
    (cells symbols : List (List Bool)) (hp : cells.map value=List.range W)
    (ha : symbols.map value=List.range (M.symbolExtra+3))
    (raw : RawRule) (r : Rule M.stateExtra M.symbolExtra) (hr : RuleEncoding raw r) :
    decodeFormula (rawRuleBody d old next cells symbols raw).1=ruleBody M (W := W) t r := by
  simp only [rawRuleBody,ruleBody,rawAppend_decode,rawForce_decode]
  rw [stateLabel_refines hd t.castSucc r.source ho hr.source_eq,
    stateLabel_refines hd t.succ r.target hn hr.target_eq]
  change force (Var.state t.castSucc r.source : TVar M W T) ++
    (force (Var.state t.succ r.target : TVar M W T) ++ _) = _
  apply congrArg (force (Var.state t.castSucc r.source : TVar M W T) ++ ·)
  apply congrArg (force (Var.state t.succ r.target : TVar M W T) ++ ·)
  apply congrArg₂ List.append
  · apply rangeFlatMap_refine cells hp
    intro bp hbp p hbpval
    rw [rawGuardComputed_decode,headLabel_refines hd t.castSucc p ho hbpval]
    change guardLiteral (pos (Var.head t.castSucc p : TVar M W T)) _ = _
    apply congrArg (guardLiteral (pos (Var.head t.castSucc p : TVar M W T)))
    simp only [rawAppend_decode,rawForce_decode]
    rw [tapeLabel_refines hd t.castSucc p r.read ho hbpval hr.read_eq,
      tapeLabel_refines hd t.succ p r.write hn hbpval hr.write_eq,
      hr.move_eq,rawHeadTarget_refines M hd t p hn hbpval r.move cells hp]
    rfl
  · apply rangeFlatMap_refine cells hp
    intro bp hbp p hbpval
    rw [rawGuardComputed_decode,headLabel_refines hd t.castSucc p ho hbpval]
    change guardLiteral (neg (Var.head t.castSucc p : TVar M W T)) _ = _
    apply congrArg (guardLiteral (neg (Var.head t.castSucc p : TVar M W T)))
    apply rangeFlatMap_refine symbols ha
    intro ba hba a hbaval
    simp only [rawCopy_decode,tapeLabel_refines hd t.castSucc p a ho hbpval hbaval,
      tapeLabel_refines hd t.succ p a hn hbpval hbaval]
    rfl

end BalancedAssortments.CookLevin
