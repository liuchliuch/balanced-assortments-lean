import BalancedAssortments.CookLevinRawRefinement

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitFormula)

structure DimensionsValid (q g W T R : ℕ) (d : RawDimensions) : Prop where
  q_eq : value d.q=q
  g_eq : value d.g=g
  w_eq : value d.w=W
  t_eq : value d.t=T
  r_eq : value d.r=R

lemma stateLabel_refines {q g W T R : ℕ} {d : RawDimensions} (hd : DimensionsValid q g W T R d)
    (t : Fin (T+1)) (s : Fin q) {bt bs : List Bool} (ht : value bt=t.val) (hs : value bs=s.val) :
    value (stateLabel d bt bs).1=index (Var.state t s : Var q g W T R) := by
  simp [stateLabel_value,ht,hs,hd.q_eq]
lemma headLabel_refines {q g W T R : ℕ} {d : RawDimensions} (hd : DimensionsValid q g W T R d)
    (t : Fin (T+1)) (p : Fin W) {bt bp : List Bool} (ht : value bt=t.val) (hp : value bp=p.val) :
    value (headLabel d bt bp).1=index (Var.head t p : Var q g W T R) := by
  simp [headLabel_value,ht,hp,hd.q_eq,hd.w_eq,hd.t_eq]
lemma tapeLabel_refines {q g W T R : ℕ} {d : RawDimensions} (hd : DimensionsValid q g W T R d)
    (t : Fin (T+1)) (p : Fin W) (a : Fin g) {bt bp ba : List Bool}
    (ht : value bt=t.val) (hp : value bp=p.val) (ha : value ba=a.val) :
    value (tapeLabel d bt bp ba).1=index (Var.tape t p a : Var q g W T R) := by
  simp [tapeLabel_value,ht,hp,ha,hd.q_eq,hd.w_eq,hd.t_eq,hd.g_eq]
lemma choiceLabel_refines {q g W T R : ℕ} {d : RawDimensions} (hd : DimensionsValid q g W T R d)
    (t : Fin T) (r : Fin R) {bt br : List Bool} (ht : value bt=t.val) (hr : value br=r.val) :
    value (choiceLabel d bt br).1=index (Var.choice t r : Var q g W T R) := by
  simp [choiceLabel_value,ht,hr,hd.q_eq,hd.w_eq,hd.t_eq,hd.g_eq,hd.r_eq]

lemma rangeFlatMap_refine {n : ℕ} (xs : List (List Bool)) (hx : xs.map value=List.range n)
    (raw : List Bool → BitFormula × ℕ) (spec : Fin n → Formula)
    (h : ∀ x∈xs,∀ i : Fin n,value x=i.val → decodeFormula (raw x).1=spec i) :
    decodeFormula (rawFlatMap raw xs).1=allFin spec := by
  rw [rawFlatMap_decode]
  have hm := rangeMap_refine xs hx (fun x => decodeFormula (raw x).1) spec h
  exact congrArg List.flatten hm

lemma rawExactlyOne_family {q g W T R n : ℕ} (xs : List (List Bool)) (hx : xs.map value=List.range n)
    (raw : List Bool → List Bool × ℕ) (f : Fin n → Var q g W T R) (hf : Function.Injective f)
    (h : ∀ x∈xs,∀ i : Fin n,value x=i.val → value (raw x).1=index (f i)) :
    decodeFormula (rawExactlyOne (rawMap raw xs).1).1=exactlyOne f := by
  have hm := rangeMap_refine xs hx (fun x => value (raw x).1) (fun i => index (f i)) h
  change ((rawExactlyOne (rawMap raw xs).1).1.map (List.map Encoding.BitLiteral.decode))=_
  rw [rawExactlyOne_decode,rawMap_eq,List.map_map]
  change exactlyOneLabels (xs.map (fun x => value (raw x).1))=_
  rw [hm,exactlyOneLabels_finRange f hf]

lemma rawShape_refines (M : Machine) {W T : ℕ} {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) d)
    (times steps states cells symbols rules : List (List Bool))
    (hTimes : times.map value=List.range (T+1)) (hSteps : steps.map value=List.range T)
    (hStates : states.map value=List.range (M.stateExtra+1)) (hCells : cells.map value=List.range W)
    (hSymbols : symbols.map value=List.range (M.symbolExtra+3)) (hRules : rules.map value=List.range (M.rules.length+1)) :
    decodeFormula (rawShape d times steps states cells symbols rules).1=shapeFormula M W T := by
  unfold rawShape shapeFormula
  rw [rawAppend_decode]
  congr 1
  · apply rangeFlatMap_refine times hTimes
    intro bt hbt t ht
    simp only [rawAppend_decode]
    congr 1
    · apply rawExactlyOne_family states hStates _ (fun s => (Var.state t s : TVar M W T))
      · intro a b he; cases he; rfl
      · intro bs hbs s hs; exact stateLabel_refines hd t s ht hs
    · congr 1
      · apply rawExactlyOne_family cells hCells _ (fun p => (Var.head t p : TVar M W T))
        · intro a b he; cases he; rfl
        · intro bp hbp p hp; exact headLabel_refines hd t p ht hp
      · apply rangeFlatMap_refine cells hCells
        intro bp hbp p hp
        apply rawExactlyOne_family symbols hSymbols _ (fun a => (Var.tape t p a : TVar M W T))
        · intro a b he; cases he; rfl
        · intro ba hba a ha; exact tapeLabel_refines hd t p a ht hp ha
  · apply rangeFlatMap_refine steps hSteps
    intro bt hbt t ht
    apply rawExactlyOne_family rules hRules _ (fun r => (Var.choice t r : TVar M W T))
    · intro a b he; cases he; rfl
    · intro br hbr r hr; exact choiceLabel_refines hd t r ht hr

end BalancedAssortments.CookLevin
