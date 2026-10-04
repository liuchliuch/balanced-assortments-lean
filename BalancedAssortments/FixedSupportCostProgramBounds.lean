import BalancedAssortments.FixedSupportCostProgram

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints
open FixedSupportCostOrder FixedSupportCostScaleList FixedSupportCostEvaluate FixedSupportCostMax
open FixedSupportCostVector (objectiveWidth)

/-- All displayed budgets below are closed polynomial expressions in the number
of coordinates and raw input bit width. No data-dependent numeric value appears. -/
def patternWidth (n A B : ℕ) : ℕ := B+(2*A+3*B+3)+scaleWidth n B+1

def patternVectorWidth (n A B : ℕ) : ℕ := vectorWidth n (patternWidth n A B)
def patternObjectiveWidth (n A B : ℕ) : ℕ := objectiveWidth n (patternWidth n A B) (patternVectorWidth n A B)

def patternCost (n A B : ℕ) : ℕ := orderCost n A B + scaleCost n B +
  (scaleCount n*(evaluationCost n (patternWidth n A B)+4)+1)+4*n+4

theorem pattern_length {I : Type*} (α K : Fraction) (ps : List (I×Product)) (ρ : Fraction) :
    (pattern α K ps ρ).1.length≤scaleCount ps.length := by
  simpa [pattern] using scalePoints_length α K ((ordered ps ρ).1.map (fun r => r.product.2))

theorem pattern_bounds {I : Type*} (α K : Fraction) (ps : List (I×Product)) (ρ : Fraction)
    {A B : ℕ} (hα : Valid α) (hK : Valid K) (hp : ∀ p∈ps,p.2.Valid) (hρ : Valid ρ)
    (hαw : width α≤B) (hKw : width K≤B) (hpw : ∀ p∈ps,p.2.Width B) (hρw : width ρ≤A) :
    (∀ out∈(pattern α K ps ρ).1,
      (∀ p∈out.1,width p.2≤patternVectorWidth ps.length A B) ∧
      width out.2≤patternObjectiveWidth ps.length A B) ∧
      (pattern α K ps ρ).2≤patternCost ps.length A B := by
  let rows := (ordered ps ρ).1
  let vs := rows.map (fun r => r.product.2)
  let scales := scalePoints α K vs
  let W := patternWidth ps.length A B
  have hrows : rows.length=ps.length := ordered_length ps ρ
  have hvs : vs.length=ps.length := by simp [vs,hrows]
  have hr : ∀ r∈rows,r.product.Valid ∧ Valid r.score := ordered_valid ps ρ hp hρ
  have hrw : ∀ r∈rows,r.product.Width B ∧ width r.score≤2*A+3*B+3 := ordered_width ps ρ hpw hρw
  have hv : ∀ v∈vs,Valid v := by
    intro v hv'
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hv'
    exact (hr r hm).1.2
  have hvw : ∀ v∈vs,width v≤B := by
    intro v hv'
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hv'
    exact (hrw r hm).1.2
  have hscv : ∀ t∈scales.1,Valid t := scalePoints_valid α K vs hα hK hv
  have hsc := scalePoints_bounds α K vs hα hK hv hαw hKw hvw
  rw [hvs] at hsc
  have hscl : scales.1.length≤scaleCount ps.length := by
    simpa [hvs] using scalePoints_length α K vs
  have heval : ∀ t∈scales.1,
      (∀ p∈(evaluateOrdered α K t rows).1.1,width p.2≤patternVectorWidth ps.length A B) ∧
      width (evaluateOrdered α K t rows).1.2≤patternObjectiveWidth ps.length A B ∧
      (evaluateOrdered α K t rows).2≤evaluationCost ps.length W := by
    intro t ht
    have hαW : width α≤W := hαw.trans (by dsimp [W,patternWidth];omega)
    have hKW : width K≤W := hKw.trans (by dsimp [W,patternWidth];omega)
    have htW : width t≤W := (hsc.1 t ht).trans (by dsimp [W,patternWidth];omega)
    have hrW : ∀ r∈rows,r.product.Width W ∧ width r.score≤W := by
      intro r hr'
      have hh := hrw r hr'
      refine ⟨⟨hh.1.1.trans ?_,hh.1.2.trans ?_⟩,hh.2.trans ?_⟩ <;> dsimp [W,patternWidth] <;> omega
    have hh := evaluateOrdered_bounds α K t rows hα hK (hscv t ht) hr hαW hKW htW hrW
    rw [hrows] at hh
    exact hh
  constructor
  · intro out hout
    obtain ⟨t,ht,rfl⟩ := (pattern_member α K ps ρ out).mp hout
    exact ⟨(heval t ht).1,(heval t ht).2.1⟩
  · have hsc' : scales.2 ≤ scaleCost ps.length B := hsc.2
    have horder := ordered_cost ps ρ hpw hρw
    have hmap := mapCost_cost (fun t => evaluateOrdered α K t rows) scales.1
      (C := evaluationCost ps.length W) (fun t ht => (heval t ht).2.2)
    have hmap' : (mapCost (fun t => evaluateOrdered α K t rows) scales.1).2 ≤
        scaleCount ps.length*(evaluationCost ps.length W+4)+1 :=
      hmap.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hscl) 1)
    change (ordered ps ρ).2+scales.2+(mapCost (fun t => evaluateOrdered α K t rows) scales.1).2+
      4*rows.length+4≤patternCost ps.length A B
    rw [hrows]
    unfold patternCost
    change _≤orderCost ps.length A B+scaleCost ps.length B+
      (scaleCount ps.length*(evaluationCost ps.length W+4)+1)+4*ps.length+4
    omega

def scoreCount (n : ℕ) : ℕ := pointCount n+(pointCount n)^2

def candidateCount (n : ℕ) : ℕ := scoreCount n*scaleCount n

def candidateCost (n B : ℕ) : ℕ := scoreCostBudget n B+
  (scoreCount n*(patternCost n (64*(B+1)) B+scaleCount n+4)+1)+4*n+4

def outputVectorWidth (n B : ℕ) : ℕ := patternVectorWidth n (64*(B+1)) B

def outputObjectiveWidth (n B : ℕ) : ℕ := patternObjectiveWidth n (64*(B+1)) B

theorem candidates_length {I : Type*} (α K : Fraction) (ps : List (I×Product)) :
    (candidates α K ps).1.length≤candidateCount ps.length := by
  let scores := (scorePoints (ps.map Prod.snd)).1
  have hs : scores.length≤scoreCount ps.length := by
    simpa [scoreCount,List.length_map] using scorePoints_length (ps.map Prod.snd)
  have hl : (scores.flatMap (fun ρ => (pattern α K ps ρ).1)).length≤scores.length*scaleCount ps.length := by
    rw [List.length_flatMap]
    have hh := List.sum_le_card_nsmul (scores.map (fun ρ => (pattern α K ps ρ).1.length))
      (scaleCount ps.length) (by
        intro x hx
        obtain ⟨ρ,_,rfl⟩ := List.mem_map.mp hx
        exact pattern_length α K ps ρ)
    simpa using hh
  change (flatMapCost (pattern α K ps) scores).1.length≤_
  rw [flatMapCost_value]
  exact hl.trans (Nat.mul_le_mul_right _ hs)

theorem candidates_bounds {I : Type*} (α K : Fraction) (ps : List (I×Product)) {B : ℕ}
    (hα : Valid α) (hK : Valid K) (hp : ∀ p∈ps,p.2.Valid)
    (hαw : width α≤B) (hKw : width K≤B) (hpw : ∀ p∈ps,p.2.Width B) :
    (∀ out∈(candidates α K ps).1,
      (∀ p∈out.1,width p.2≤outputVectorWidth ps.length B) ∧
      width out.2≤outputObjectiveWidth ps.length B) ∧
      (candidates α K ps).2≤candidateCost ps.length B := by
  let products := ps.map Prod.snd
  let scores := scorePoints products
  have hB : 1≤B := (valid_width_positive α hα).trans hαw
  have hv : ∀ p∈products,p.Valid := by
    intro p hm
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact hp x hx
  have hw : ∀ p∈products,p.Width B := by
    intro p hm
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact hpw x hx
  have hsv : ∀ ρ∈scores.1,Valid ρ := scorePoints_valid products hv
  have hsw : ∀ ρ∈scores.1,width ρ≤64*(B+1) := scorePoints_width products hB hv hw
  have hsc : scores.2≤scoreCostBudget ps.length B := by
    simpa [products,List.length_map] using scorePoints_cost products hB hv hw
  have hsl : scores.1.length≤scoreCount ps.length := by
    simpa [products,scoreCount,List.length_map] using scorePoints_length products
  have hpat : ∀ ρ∈scores.1,
      (∀ out∈(pattern α K ps ρ).1,
        (∀ p∈out.1,width p.2≤outputVectorWidth ps.length B) ∧
        width out.2≤outputObjectiveWidth ps.length B) ∧
      (pattern α K ps ρ).2≤patternCost ps.length (64*(B+1)) B := by
    intro ρ hρ
    exact pattern_bounds α K ps ρ hα hK hp (hsv ρ hρ) hαw hKw hpw (hsw ρ hρ)
  constructor
  · intro out hout
    obtain ⟨ρ,hρ,hout⟩ := (candidates_member α K ps out).mp hout
    exact (hpat ρ hρ).1 out hout
  · have hflat := flatMapCost_cost (pattern α K ps) scores.1
      (C := patternCost ps.length (64*(B+1)) B) (H := scaleCount ps.length)
      (fun ρ hρ => ⟨(hpat ρ hρ).2,pattern_length α K ps ρ⟩)
    have hflat' : (flatMapCost (pattern α K ps) scores.1).2≤
        scoreCount ps.length*(patternCost ps.length (64*(B+1)) B+scaleCount ps.length+4)+1 :=
      hflat.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hsl) 1)
    change scores.2+(flatMapCost (pattern α K ps) scores.1).2+4*ps.length+4≤candidateCost ps.length B
    unfold candidateCost
    omega

/-- Closed polynomial binary/list-machine bound for the entire exact-support
program: score/scale enumeration, stable sorting, raw greedy evaluation, and
selection of the largest cached objective are all included. -/
def runCost (n B : ℕ) : ℕ := candidateCost n B+
  (candidateCount n*(2048*(2*outputObjectiveWidth n B+1)^2+8)+3)+4

theorem runBits_cost {I : Type*} (α K : Fraction) (ps : List (I×Product)) {B : ℕ}
    (hα : Valid α) (hK : Valid K) (hp : ∀ p∈ps,p.2.Valid)
    (hαw : width α≤B) (hKw : width K≤B) (hpw : ∀ p∈ps,p.2.Width B) :
    (runBits α K ps).2≤runCost ps.length B := by
  have hc := candidates_bounds α K ps hα hK hp hαw hKw hpw
  have hl := candidates_length α K ps
  have hb := best_cost (candidates α K ps).1 (fun out hout => (hc.1 out hout).2)
  have hb' : (best (candidates α K ps).1).2≤
      candidateCount ps.length*(2048*(2*outputObjectiveWidth ps.length B+1)^2+8)+3 :=
    hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 3)
  dsimp only [runBits,runCost]
  omega

theorem runBits_width {I : Type*} (α K : Fraction) (ps : List (I×Product)) {B : ℕ}
    (hα : Valid α) (hK : Valid K) (hp : ∀ p∈ps,p.2.Valid)
    (hαw : width α≤B) (hKw : width K≤B) (hpw : ∀ p∈ps,p.2.Width B)
    {out : Result I} (hout : (runBits α K ps).1=some out) :
    (∀ p∈out.1,width p.2≤outputVectorWidth ps.length B) ∧
      width out.2≤outputObjectiveWidth ps.length B :=
  (candidates_bounds α K ps hα hK hp hαw hKw hpw).1 out (runBits_member α K ps hout)

end BalancedAssortments.FixedSupportCostProgram
