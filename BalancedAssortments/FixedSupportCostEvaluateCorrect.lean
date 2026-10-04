import BalancedAssortments.FixedSupportCostEvaluate
import BalancedAssortments.FixedSupportCandidateFeasibility

namespace BalancedAssortments.FixedSupportCostEvaluate
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars
open FixedSupportCostOrder FixedSupportCostVector FixedSupportAlgorithm

private theorem row_map {n : ℕ} {β : Type*} (rows : List (Scored (Fin n))) (o : List (Fin n))
    (ho : rows.map Scored.label=o) (f : Scored (Fin n)→β) (g : Fin n→β)
    (h : ∀ s ∈ rows,f s=g s.label) : rows.map f=o.map g := by
  rw [← ho,List.map_map]
  apply List.map_congr_left
  exact h

theorem rationalAllocation_eq {n : ℕ} (r v : Fin n→ℚ) (ρ : ℚ) (α K t : Fraction)
    (rows : List (Scored (Fin n)))
    (ho : rows.map Scored.label=scoreOrder r v ρ)
    (hd : ∀ s ∈ rows,decode s.product.2=v s.label ∧ decode s.score=score r v ρ s.label) :
    rationalAllocation α K t rows =
      (ContinuousKnapsack.solve (rationalBudget v (decode K) (decode t))
        (knapsackItems r v (decode α) ρ (decode t))).1 := by
  have hv := row_map rows _ ho (fun s => 1/decode s.product.2) (fun i => 1/v i)
    (fun s hs => by dsimp only; rw [(hd s hs).1])
  have hi := row_map rows _ ho
    (fun s => (⟨decode s.score,min 1 (decode t/(decode α*decode s.product.2))-
      decode t/decode s.product.2⟩ : ContinuousKnapsack.Item))
    (fun i => (⟨score r v ρ i,rationalCap v (decode α) (decode t) i⟩ : ContinuousKnapsack.Item))
    (fun s hs => by dsimp only; rw [(hd s hs).1,(hd s hs).2];rfl)
  unfold rationalAllocation
  rw [hv,hi,sum_order _ (scoreOrder_perm r v ρ)]
  rfl

theorem evaluateOrdered_candidate {n : ℕ} (r v : Fin n→ℚ) (ρ : ℚ) (α K t : Fraction)
    (rows : List (Scored (Fin n)))
    (hα : Valid α) (hK : Valid K) (ht : Valid t)
    (hr : ∀ s ∈ rows,s.product.Valid ∧ Valid s.score)
    (ho : rows.map Scored.label=scoreOrder r v ρ)
    (hd : ∀ s ∈ rows,decode s.product.2=v s.label ∧ decode s.score=score r v ρ s.label) :
    (evaluateOrdered α K t rows).1.1.map (fun p => (p.1,decode p.2)) =
      (scoreOrder r v ρ).map (fun i => (i,candidateVector r v (decode α) (decode K) (ρ,decode t) i)) := by
  let o := scoreOrder r v ρ
  let y := (ContinuousKnapsack.solve (rationalBudget v (decode K) (decode t))
    (knapsackItems r v (decode α) ρ (decode t))).1
  have hy : y.length=o.length := by simp [y,o,knapsackItems,ContinuousKnapsack.solve_length]
  have hrec := recover_map o y (scoreOrder_nodup r v ρ) hy
  have hrec' : rows.map (fun s => recover o y s.label)=y := by
    change rows.map (recover o y ∘ Scored.label)=y
    rw [← List.map_map,ho,hrec]
  rw [evaluateOrdered_decode _ _ _ _ hα hK ht hr,rationalAllocation_eq r v ρ α K t rows ho hd]
  change (rows.zip y).map _ = _
  rw [← hrec']
  have hz : rows.zip (rows.map (fun s => recover o y s.label)) =
      rows.map (fun s => (s,recover o y s.label)) := by
    simpa only [List.map_id,id_eq] using (List.zip_map' (f := id) (g := fun s => recover o y s.label) (l := rows))
  rw [hz]
  simp only [List.map_map,Function.comp_def]
  apply row_map rows _ ho
  intro s hs
  simp only [Prod.map,Prod.fst,Prod.snd,id_eq,(hd s hs).1]
  rfl

theorem evaluateOrdered_revenue {n : ℕ} (r v : Fin n→ℚ) (ρ : ℚ) (α K t : Fraction)
    (rows : List (Scored (Fin n)))
    (hα : Valid α) (hK : Valid K) (ht : Valid t)
    (hr : ∀ s ∈ rows,s.product.Valid ∧ Valid s.score)
    (ho : rows.map Scored.label=scoreOrder r v ρ)
    (hd : ∀ s ∈ rows,decode s.product.1=r s.label ∧
      decode s.product.2=v s.label ∧ decode s.score=score r v ρ s.label) :
    decode (evaluateOrdered α K t rows).1.2 =
      fractionalRevenue r (candidateVector r v (decode α) (decode K) (ρ,decode t)) := by
  let c := candidateVector r v (decode α) (decode K) (ρ,decode t)
  let o := scoreOrder r v ρ
  let ws := (evaluateOrdered α K t rows).1.1
  have hc := evaluateOrdered_candidate r v ρ α K t rows hα hK ht hr ho (fun s hs => (hd s hs).2)
  have hweights : ws.map (fun p => decode p.2)=o.map c := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map Prod.snd) hc
  have hprices : (rows.map (fun s => s.product.1)).map decode=o.map r := by
    simp only [List.map_map,Function.comp_def]
    exact row_map rows o ho _ r (fun s hs => (hd s hs).1)
  have hnum : (((rows.map (fun r => r.product.1)).zip (ws.map Prod.snd)).map
      (fun p => decode p.1*decode p.2)).sum = ∑ i,r i*c i := by
    have hz : (((rows.map (fun s => s.product.1)).zip (ws.map Prod.snd)).map
        (fun p => decode p.1*decode p.2)) =
        (((rows.map (fun s => s.product.1)).map decode).zip
          ((ws.map Prod.snd).map decode)).map (fun p => p.1*p.2) := by
      simp only [List.zip_map,List.map_map,Function.comp_def]
      rfl
    rw [hz,hprices]
    simp only [List.map_map,Function.comp_def]
    rw [hweights,List.zip_map']
    simp only [List.map_map,Function.comp_def]
    exact sum_order o (scoreOrder_perm r v ρ) _
  rw [evaluateOrdered_objective _ _ _ _ hα hK ht hr]
  change _ / (1+(ws.map (fun p => decode p.2)).sum)=_
  rw [hnum,hweights,sum_order o (scoreOrder_perm r v ρ)]
  rfl

theorem evaluate_ordered_candidate {n : ℕ} (r v : Fin n→ℚ) (ps : List (Fin n×Product))
    (ρ α K t : Fraction) (hlabels : ps.map Prod.fst=List.finRange n)
    (hp : ∀ p ∈ ps,p.2.Valid) (hρ : Valid ρ) (hα : Valid α) (hK : Valid K) (ht : Valid t)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1) :
    (evaluateOrdered α K t (ordered ps ρ).1).1.1.map (fun p => (p.1,decode p.2)) =
      (scoreOrder r v (decode ρ)).map (fun i =>
        (i,candidateVector r v (decode α) (decode K) (decode ρ,decode t) i)) ∧
    decode (evaluateOrdered α K t (ordered ps ρ).1).1.2 =
      fractionalRevenue r (candidateVector r v (decode α) (decode K) (decode ρ,decode t)) := by
  have hd : ∀ s ∈ (ordered ps ρ).1,decode s.product.1=r s.label ∧
      decode s.product.2=v s.label ∧ decode s.score=score r v (decode ρ) s.label := by
    intro s hs
    have hm := ordered_member ps ρ hs
    have hh := hdata _ hm.1
    refine ⟨hh.1,hh.2,?_⟩
    rw [hm.2,scoreBits_decode _ _ (hp _ hm.1) hρ,hh.1,hh.2]
    rfl
  have ho := ordered_labels r v ps ρ hlabels hp hρ hdata
  have hv := ordered_valid ps ρ hp hρ
  exact ⟨evaluateOrdered_candidate r v (decode ρ) α K t _ hα hK ht hv ho (fun s hs => (hd s hs).2),
    evaluateOrdered_revenue r v (decode ρ) α K t _ hα hK ht hv ho hd⟩

end BalancedAssortments.FixedSupportCostEvaluate
