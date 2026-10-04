import BalancedAssortments.CookLevinRawCostBasic

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitFormula)

structure CostProfile where
  len : ℕ
  cost : ℕ

def CostProfile.append (p q : CostProfile) : CostProfile := ⟨p.len+q.len,p.cost+q.cost+p.len+4⟩
def CostProfile.loop (N : ℕ) (p : CostProfile) : CostProfile := ⟨N*p.len,N*(p.cost+p.len+4)+1⟩
def CostProfile.guarded (b : ℕ) (p : CostProfile) : CostProfile := ⟨p.len,labelCost b+p.cost+8*p.len+5⟩
def familyProfile (N b : ℕ) : CostProfile := ⟨familyLength N,familyCost N b⟩
def copyProfile (b : ℕ) : CostProfile := ⟨1,2*labelCost b+8⟩
def forceProfile (b : ℕ) : CostProfile := ⟨1,labelCost b+6⟩
def shapeProfile (N b : ℕ) : CostProfile :=
  (CostProfile.loop N ((familyProfile N b).append
    ((familyProfile N b).append (CostProfile.loop N (familyProfile N b))))).append
    (CostProfile.loop N (familyProfile N b))

def ListWidths (b : ℕ) (xs : List (List Bool)) : Prop := ∀ x∈xs,x.length≤b

lemma rawShape_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    (times steps states cells symbols rules : List (List Bool))
    (nt : times.length≤N) (ns : steps.length≤N) (nq : states.length≤N)
    (nw : cells.length≤N) (ng : symbols.length≤N) (nr : rules.length≤N)
    (ht : ListWidths b times) (hs : ListWidths b steps) (hq : ListWidths b states)
    (hw : ListWidths b cells) (hg : ListWidths b symbols) (hr : ListWidths b rules) :
    CodeBound (shapeProfile N b).len (shapeProfile N b).cost (rawShape d times steps states cells symbols rules) := by
  apply bound_append
  · apply bound_flatMap times _ nt
    intro time htime
    apply bound_append
    · exact bound_family states _ nq (fun s h => stateLabel_bounds hd (ht time htime) (hq s h))
    · apply bound_append
      · exact bound_family cells _ nw (fun p h => headLabel_bounds hd (ht time htime) (hw p h))
      · apply bound_flatMap cells _ nw
        intro cell hcell
        exact bound_family symbols _ ng (fun a h => tapeLabel_bounds hd (ht time htime) (hw cell hcell) (hg a h))
  · apply bound_flatMap steps _ ns
    intro time htime
    exact bound_family rules _ nr (fun r h => choiceLabel_bounds hd (hs time htime) (hr r h))

def acceptProfile (N b : ℕ) : CostProfile := ⟨1,N*(labelCost b+4)+6*N+6⟩
lemma rawAccept_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {time : List Bool} (ht : time.length≤b) (accepting : List (List Bool))
    (hn : accepting.length≤N) (ha : ListWidths b accepting) :
    CodeBound (acceptProfile N b).len (acceptProfile N b).cost (rawAccept d time accepting) := by
  have hm := rawMap_cost (stateLabel d time) accepting (labelCost b)
    (fun x hx => (stateLabel_bounds hd ht (ha x hx)).2)
  have hs := rawMap_cost (fun x : List Bool => (Encoding.bitPositive x,2))
    (rawMap (stateLabel d time) accepting).1 2 (by simp)
  have hl : (rawMap (stateLabel d time) accepting).1.length=accepting.length := by simp [rawMap_eq]
  rw [hl] at hs
  constructor
  · rfl
  · simp only [rawAccept,rawSingle,acceptProfile]
    have hh := Nat.mul_le_mul_right (labelCost b+4) hn
    omega

def haltProfile (N b : ℕ) : CostProfile :=
  (acceptProfile N b).append ((CostProfile.loop N (copyProfile b)).append
    ((CostProfile.loop N (copyProfile b)).append (CostProfile.loop N (CostProfile.loop N (copyProfile b)))))

lemma rawHaltBody_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {old next : List Bool} (ho : old.length≤b) (hn : next.length≤b)
    (states cells symbols accepting : List (List Bool))
    (ns : states.length≤N) (nc : cells.length≤N) (na : symbols.length≤N) (nacc : accepting.length≤N)
    (hs : ListWidths b states) (hc : ListWidths b cells) (ha : ListWidths b symbols) (hacc : ListWidths b accepting) :
    CodeBound (haltProfile N b).len (haltProfile N b).cost (rawHaltBody d old next states cells symbols accepting) := by
  apply bound_append (rawAccept_bound hd ho accepting nacc hacc)
  apply bound_append
  · apply bound_flatMap states _ ns
    intro s h
    exact bound_copy (stateLabel_bounds hd ho (hs s h)).2 (stateLabel_bounds hd hn (hs s h)).2
  · apply bound_append
    · apply bound_flatMap cells _ nc
      intro p h
      exact bound_copy (headLabel_bounds hd ho (hc p h)).2 (headLabel_bounds hd hn (hc p h)).2
    · apply bound_flatMap cells _ nc
      intro p hp
      apply bound_flatMap symbols _ na
      intro a haa
      exact bound_copy (tapeLabel_bounds hd ho (hc p hp) (ha a haa)).2 (tapeLabel_bounds hd hn (hc p hp) (ha a haa)).2

end BalancedAssortments.CookLevin
