import BalancedAssortments.NPStackSourceVerifierFinalState
import BalancedAssortments.NPStackSourceBalanceBound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

/-- A constant derived only from the fixed finite arithmetic control syntax. -/
def widthCoefficient : Command → ℕ
  | .halt _ => 1
  | .script ops next => widthCoefficient next*3^ops.length
  | .branchLE _ _ yes no => widthCoefficient yes+widthCoefficient no

lemma command_width (c : Command) (s : Registers) (L : ℕ)
    (hs : ∀ k,width (s k)+1≤L) : ∀ k,width ((eval c s).2 k)+1≤widthCoefficient c*L := by
  induction c generalizing s L with
  | halt b => simpa [eval,widthCoefficient] using hs
  | script ops next ih =>
    have h:=ih (evalAssignments ops s) (3^ops.length*L) (assignments_size ops s hs)
    simpa [eval,widthCoefficient,Nat.mul_assoc] using h
  | branchLE a b yes no ihy ihn =>
    intro k
    have hy:=ihy s L hs k
    have hn:=ihn s L hs k
    simp only [eval,widthCoefficient]
    split_ifs <;> nlinarith

lemma clean_width (s : Registers) (W : ℕ) (hs : ∀ k,width (s k)≤W) :
    ∀ k,width (Whole.cleanRegisters s k)≤W := by
  intro k
  have hk:=hs k
  cases k <;> simp only [Whole.cleanRegisters,loadRecord,Whole.emptyRecord] <;>
    first | exact hk | (simp [width,zzero])

def rankWidth (W : ℕ) : ℕ := widthCoefficient VerifierCommands.rankCommand*(W+1)
def finalWidth (W : ℕ) : ℕ := widthCoefficient VerifierCommands.revenueCommand*rankWidth W

def scalarBudget (W : ℕ) : ℕ :=
  (costCoefficient VerifierCommands.headerCommand+costCoefficient VerifierCommands.rankCommand)*(W+1)^2+
  costCoefficient VerifierCommands.revenueCommand*(rankWidth W)^2

lemma final_width (s : Registers) (W : ℕ) (hs : ∀ k,width (s k)≤W) :
    ∀ k,width (finalRegisters s k)≤finalWidth W := by
  have hc:=clean_width s W hs
  have hr:=command_width VerifierCommands.rankCommand (Whole.cleanRegisters s) (W+1)
    (fun k=>by have h:=hc k;omega)
  have hv:=command_width VerifierCommands.revenueCommand
    (eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).2 (rankWidth W) hr
  intro k
  have hh:=hv k
  change width (finalRegisters s k)+1≤finalWidth W at hh
  omega

lemma scalar_budget_bound (s : Registers) (W : ℕ) (hs : ∀ k,width (s k)≤W) :
    budget VerifierCommands.compareTime VerifierCommands.headerCommand (Whole.cleanRegisters s)+
    budget VerifierCommands.compareTime VerifierCommands.rankCommand (Whole.cleanRegisters s)+
    budget VerifierCommands.compareTime VerifierCommands.revenueCommand
      (eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).2 ≤ scalarBudget W := by
  have hc:=clean_width s W hs
  have hcw : ∀ k,width (Whole.cleanRegisters s k)+1≤W+1 := fun k=>by have h:=hc k;omega
  have hh:=budget_quadratic VerifierCommands.headerCommand (Whole.cleanRegisters s) hcw
  have hr:=budget_quadratic VerifierCommands.rankCommand (Whole.cleanRegisters s) hcw
  have hw:=command_width VerifierCommands.rankCommand (Whole.cleanRegisters s) (W+1) hcw
  have hv:=budget_quadratic VerifierCommands.revenueCommand
    (eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).2 hw
  unfold scalarBudget rankWidth
  nlinarith

def finalBalanceBudget (n W B : ℕ) : ℕ := scalarBudget W+n*Balance.rowBound (finalWidth W+B)+1

theorem final_balance_bounded (s u : Registers) (xs : List Balance.Triple) (W B : ℕ)
    (hs : ∀ k,width (s k)≤W) (hx : ∀ x∈xs,∀ i,(x i).length≤B)
    (h : Balance.loopValue (finalRegisters s) xs=some u) :
    ∃ t,Run Balance.loopProgram t ⟨.probe,Balance.stable (finalRegisters s) (Balance.stream xs)⟩
        ⟨.accept,Balance.stable u []⟩ ∧
      budget VerifierCommands.compareTime VerifierCommands.headerCommand (Whole.cleanRegisters s)+
      budget VerifierCommands.compareTime VerifierCommands.rankCommand (Whole.cleanRegisters s)+
      budget VerifierCommands.compareTime VerifierCommands.revenueCommand
        (eval VerifierCommands.rankCommand (Whole.cleanRegisters s)).2+t ≤ finalBalanceBudget xs.length W B := by
  obtain ⟨t,ht,hr⟩ := Balance.loop_success_polynomial (finalRegisters s) u xs (finalWidth W+B)
    (fun k=>(final_width s W hs k).trans (by omega))
    (fun x hx' i=>(hx x hx' i).trans (by omega)) h
  exact ⟨t,hr,by have hh:=scalar_budget_bound s W hs;unfold finalBalanceBudget;omega⟩

end BalancedAssortments.NPStack.SourceVerifier
