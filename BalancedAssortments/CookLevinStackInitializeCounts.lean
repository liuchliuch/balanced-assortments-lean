import BalancedAssortments.CookLevinStackInitialize

noncomputable section
namespace BalancedAssortments.CookLevin.StackInitialize
open NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)

def setBits (k : ℕ) (bits : List Bool) : Block ℕ :=
  .seq (clearStack k) (StackIndices.pushBits k bits)
lemma setBits_exec (k : ℕ) (bits : List Bool) (s : Store ℕ) :
    Exec (setBits k bits) s (Function.update s k bits)
      (3*(s k).length+2*bits.length+3) := by
  have ha := clearStack_exec k s
  have hb := StackIndices.pushBits_exec k bits (Function.update s k [])
  convert Exec.seq ha hb using 1 <;> simp [setBits,Function.update_idem] <;> omega

def setBatch : List (ℕ × List Bool) → Block ℕ
  | [] => .skip
  | b::bs => .seq (setBits b.1 b.2) (setBatch bs)
def setBatchCost (s : Store ℕ) : List (ℕ × List Bool) → ℕ
  | [] => 1
  | b::bs => 3*(s b.1).length+2*b.2.length+3+setBatchCost (Function.update s b.1 b.2) bs+1
lemma setBatch_exec (s : Store ℕ) (bs : List (ℕ × List Bool)) :
    Exec (setBatch bs) s (Macros.writes s bs) (setBatchCost s bs) := by
  induction bs generalizing s with
  | nil => exact Exec.skip s
  | cons b bs ih => exact Exec.seq (setBits_exec b.1 b.2 s) (ih _)

def countBatch : List (Fin 9 × ℕ) → Block ℕ
  | [] => .skip
  | b::bs => .seq (StackCount.countFuel 100 b.2 21 20 b.1) (countBatch bs)
def countBindings (s : Store ℕ) (bs : List (Fin 9 × ℕ)) : List (ℕ × List Bool) :=
  bs.map (fun b => (b.1.val,StackCount.counterBits (s b.2).length))
def countBatchBudget (B : ℕ) : List (Fin 9 × ℕ) → ℕ
  | [] => 1
  | b::bs => StackCount.countBudget b.1 B B+countBatchBudget B bs+1

lemma countBatch_exec (s : Store ℕ) (bs : List (Fin 9 × ℕ)) (B : ℕ)
    (hfuel : ∀ b∈bs,9≤b.2 ∧ b.2<20 ∧ s b.2=List.replicate (s b.2).length false)
    (hb : ∀ b∈bs,(s b.2).length+1≤B)
    (hfields : ∀ i : Fin 9,(s i.val).length≤B)
    (hclean : ∀ k,20≤k → s k=[]) :
    ∃ t≤countBatchBudget B bs,Exec (countBatch bs) s (Macros.writes s (countBindings s bs)) t := by
  induction bs generalizing s with
  | nil => exact ⟨1,le_rfl,Exec.skip s⟩
  | cons b bs ih =>
    have hfb := hfuel b (by simp)
    have hbb := hb b (by simp)
    have hi : Function.Injective (Macros.copyMap b.2 21 20) := by
      intro i j he;cases i <;> cases j <;> simp only [Macros.copyMap] at he <;> first | rfl | omega
    obtain ⟨t,ht,hr⟩ := StackCount.countFuel_exec 100 b.2 21 20 b.1 s (s b.2).length B
      (by omega) (by omega) (by omega) hfb.1 (by omega) hi hfb.2.2
      (hclean 21 (by omega)) (hclean 20 (by omega))
      (fun k hk _ => hclean k (by omega)) hfields hbb
    let u := Function.update s b.1.val (StackCount.counterBits (s b.2).length)
    have hulow : ∀ k,9≤k → u k=s k := by
      intro k hk
      exact Function.update_of_ne (by have := b.1.isLt;omega) _ _
    have hufuel : ∀ c∈bs,9≤c.2 ∧ c.2<20 ∧ u c.2=List.replicate (u c.2).length false := by
      intro c hc
      have hf := hfuel c (by simp [hc])
      rw [hulow c.2 hf.1]
      exact hf
    have hub : ∀ c∈bs,(u c.2).length+1≤B := by
      intro c hc
      rw [hulow c.2 (hfuel c (by simp [hc])).1]
      exact hb c (by simp [hc])
    have huw : ∀ i : Fin 9,(u i.val).length≤B := by
      intro i
      by_cases he : i.val=b.1.val
      · simp only [u,he,Function.update_self]
        exact (StackCount.counterBits_width _).trans hbb
      · simpa [u,Function.update,he] using hfields i
    have huc : ∀ k,20≤k → u k=[] := by
      intro k hk;rw [hulow k (by omega)];exact hclean k hk
    obtain ⟨t',ht',hr'⟩ := ih u hufuel hub huw huc
    have hbindings : countBindings u bs=countBindings s bs := by
      apply List.map_congr_left
      intro c hc
      rw [hulow c.2 (hfuel c (by simp [hc])).1]
    rw [hbindings] at hr'
    refine ⟨t+t'+1,?_,Exec.seq hr hr'⟩
    have htb : StackCount.countBudget b.1 (s b.2).length B≤StackCount.countBudget b.1 B B := by
      unfold StackCount.countBudget
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 5 (by omega)) _) (Nat.mul_le_mul_right _ (by omega))) _
    simp only [countBatchBudget]
    omega

end BalancedAssortments.CookLevin.StackInitialize
