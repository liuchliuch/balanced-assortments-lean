import BalancedAssortments.CookLevinStackAssign
import BalancedAssortments.NPStackStructuredLoops
import BalancedAssortments.FPTASCostInputSeeds

/-! Operational binary counting of a real unary fuel stack. The loop reads
physical bits, preserves its source fuel, and writes an actual binary counter. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackCount
open NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackAssign

def counterBits (m : ℕ) : List Bool := (FPTASCostSeeds.countBits (List.replicate m ())).1
@[simp] lemma counterBits_zero : counterBits 0=[] := rfl
lemma counterBits_succ (m : ℕ) : counterBits (m+1)=(addCarry (counterBits m) [true] false).1 := by
  simp [counterBits,List.replicate_succ,FPTASCostSeeds.countBits]
lemma counterBits_value (m : ℕ) : value (counterBits m)=m := by simp [counterBits,FPTASCostSeeds.countBits_value]
lemma counterBits_width (m : ℕ) : (counterBits m).length≤ m+1 := by
  simpa [counterBits] using FPTASCostSeeds.countBits_width (List.replicate m ())

def countFuel {n : ℕ} (base fuel scratch counter : ℕ) (dest : Fin n) : Block ℕ :=
  .seq (clearStack dest.val) (forFuel fuel scratch counter (increment base dest))

def countBudget {n : ℕ} (dest : Fin n) (m B : ℕ) : ℕ :=
  3*B+5*m+m*((assignTime (incrementExpr dest)).eval B+2)+6

/-- Full operational invariant: only the selected binary field changes; the
unary fuel, scratch and consumed counter all regain their initial contents. -/
theorem countFuel_exec {n : ℕ} (base fuel scratch counter : ℕ) (dest : Fin n)
    (s : Store ℕ) (m B : ℕ)
    (hbase : n≤base) (hcounter : n≤counter) (hcounterBase : counter<base)
    (hfuel : n≤fuel) (hscratch : n≤scratch)
    (hinj : Function.Injective (Macros.copyMap fuel scratch counter))
    (hsFuel : s fuel=List.replicate m false) (hsScratch : s scratch=[]) (hsCounter : s counter=[])
    (hwork : Fresh s base (StackIndices.slots (incrementExpr dest)))
    (hwidth : ∀ i : Fin n,(s i.val).length≤B) (hmB : m+1≤B) :
    ∃ t≤countBudget dest m B,
      Exec (countFuel base fuel scratch counter dest) s (Function.update s dest.val (counterBits m)) t := by
  have hdest := dest.isLt
  have hdc : dest.val≠counter := by omega
  have hdf : dest.val≠fuel := by omega
  have hds : dest.val≠scratch := by omega
  let cleared := Function.update s dest.val []
  have hclear := clearStack_exec dest.val s
  have cfuel : cleared fuel=List.replicate m false := by simp [cleared,Function.update,Ne.symm hdf,hsFuel]
  have cscratch : cleared scratch=[] := by simp [cleared,Function.update,Ne.symm hds,hsScratch]
  have ccounter : cleared counter=[] := by simp [cleared,Function.update,Ne.symm hdc,hsCounter]
  let Inv := fun i (u : Store ℕ) =>
    u dest.val=counterBits i ∧ i+(u counter).length=m ∧
      ∀ k,k≠dest.val → k≠counter → u k=s k
  have hstart : Inv 0 (Function.update cleared counter (List.replicate m false)) := by
    constructor
    · simp [Inv,cleared,Function.update,hdc]
    constructor
    · simp
    · intro k hk1 hk2;simp [cleared,Function.update,hk1,hk2]
  have hstep : ∀ i u rest,Inv i u → u counter=false::rest →
      ∃ v t,t≤(assignTime (incrementExpr dest)).eval B ∧
        Exec (increment base dest) (Function.update u counter rest) v t ∧ v counter=rest ∧ Inv (i+1) v := by
    intro i u rest hu hc
    obtain ⟨hud,hum,huf⟩ := hu
    have him : i≤ m := by omega
    let before := Function.update u counter rest
    have hbd : before dest.val=counterBits i := by simp [before,Function.update,hdc,hud]
    have hw : ∀ j : Fin n,(before j.val).length≤B := by
      intro j
      by_cases he : j.val=dest.val
      · rw [he,hbd]
        exact (counterBits_width i).trans (by omega)
      · have hjc : j.val≠counter := by have := j.isLt;omega
        simpa [before,Function.update,hjc,huf j.val he hjc] using hwidth j
    have hf : Fresh before base (StackIndices.slots (incrementExpr dest)) := by
      intro k hkl hkr
      have hkd : k≠dest.val := by omega
      have hkc : k≠counter := by omega
      simpa [before,Function.update,hkc,huf k hkd hkc] using hwork k hkl hkr
    obtain ⟨t,ht,hr⟩ := assignExpr_exec base dest (incrementExpr dest) before B hbase hf hw
    have hbits : ((incrementExpr dest).run (StackIndices.inputView n before)).1=counterBits (i+1) := by
      rw [increment_result,hbd,counterBits_succ]
    rw [hbits] at hr
    let after := Function.update before dest.val (counterBits (i+1))
    refine ⟨after,t,ht,hr,?_,?_⟩
    · simp [after,before,Function.update,Ne.symm hdc]
    constructor
    · simp [after]
    constructor
    · have hlen : i+(rest.length+1)=m := by simpa [hc] using hum
      simpa [after,before,Function.update,Ne.symm hdc] using (show i+1+rest.length=m by omega)
    · intro k hk1 hk2
      simpa [after,before,Function.update,hk1,hk2] using huf k hk1 hk2
  obtain ⟨u,t,ht,hr,huc,hu⟩ := forFuel_bounded fuel scratch counter (increment base dest) hinj Inv
    ((assignTime (incrementExpr dest)).eval B) m cleared cfuel cscratch ccounter hstart hstep
  have hend : u=Function.update s dest.val (counterBits m) := by
    obtain ⟨hd,hcount,hframe⟩ := hu
    funext k
    by_cases hk : k=dest.val
    · subst k;simpa using hd
    · by_cases hc : k=counter
      · subst k;simp [Function.update,Ne.symm hdc,hsCounter,huc]
      · simpa [Function.update,hk] using hframe k hk hc
  rw [hend] at hr
  refine ⟨(3*(s dest.val).length+1)+t+1,?_,Exec.seq hclear hr⟩
  have hdwidth := hwidth dest
  unfold countBudget
  omega

end BalancedAssortments.CookLevin.StackCount
