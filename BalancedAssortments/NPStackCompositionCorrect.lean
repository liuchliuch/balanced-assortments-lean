import BalancedAssortments.NPStackCompositionRuns

namespace BalancedAssortments.NPStack.Composition
open NPStack
variable {K₁ Q₁ K₂ Q₂ : Type*} [DecidableEq K₁] [DecidableEq K₂]

lemma initial_cfg (P : Program K₁ Q₁) (R : Program K₂ Q₂) (word : List Bool) :
    initial (program P R) word=cfg (.first P.start) (initial P word).stk (fun _ => []) [] := by
  unfold initial cfg
  congr 1
  funext k
  cases k with
  | inl k => simp [program,store,firstStack,Function.update]
  | inr k => cases k <;> simp [program,store,firstStack,Function.update]

lemma first_return (P : Program K₁ Q₁) (R : Program K₂ Q₂) (q : Q₁)
    (h : P.code q=.halt true) (s : K₁→List Bool) (t : K₂→List Bool) (u : List Bool) :
    Step (program P R) (cfg (.first q) s t u) (cfg (.transfer false .read) s t u) := by
  simp [Step,successors,program,h,cfg]

lemma transfer_return (P : Program K₁ Q₁) (R : Program K₂ Q₂) (stage : Bool)
    (s : K₁→List Bool) (t : K₂→List Bool) (u : List Bool) :
    Step (program P R) (cfg (.transfer stage .done) s t u)
      (cfg (if stage then .second R.start else .transfer true .read) s t u) := by
  cases stage <;> simp [Step,successors,program,cfg]

/-- Literal finite transducer composition, including every output-transfer
cell and every subroutine return transition. -/
theorem outputs_compose (P : Program K₁ Q₁) (R : Program K₂ Q₂)
    (word middle output : List Bool) {T U : ℕ}
    (hp : OutputsIn P word middle T) (hr : OutputsIn R middle output U) :
    OutputsIn (program P R) word output (T+U+4*middle.length+5) := by
  obtain ⟨t,ht,c,hc,haccept,hout⟩ := hp
  obtain ⟨u,hu,d,hd,hdaccept,hdout⟩ := hr
  let s := Function.update c.stk P.outputStack []
  let z : K₂→List Bool := fun _ => []
  have hfirst := first_run R hc z []
  have hi : cfg (.first (initial P word).pc) (initial P word).stk z [] = initial (program P R) word :=
    (initial_cfg P R word).symm
  rw [hi] at hfirst
  have hj1 := first_return P R c.pc haccept c.stk z []
  have hm1 := transfer_first P R c.stk z []
  rw [hout] at hm1
  simp only [List.append_nil] at hm1
  have hj2 := transfer_return P R false s z middle.reverse
  have hm2 := transfer_second P R s z middle.reverse
  simp only [List.length_reverse,List.reverse_reverse] at hm2
  have he : Function.update z R.inputStack (middle++z R.inputStack)=(initial R middle).stk := by
    simp [z,initial]
  rw [he] at hm2
  have hj3 := transfer_return P R true s (initial R middle).stk []
  have hsecond := second_run P hd s []
  have hall := (((((hfirst.trans (Run.one hj1)).trans hm1).trans (Run.one hj2)).trans hm2).trans
    (Run.one hj3)).trans hsecond
  refine ⟨_,?_,cfg (.second d.pc) s d.stk [],hall,?_,?_⟩
  · omega
  · change (R.code d.pc).rename secondStack Label.second=.halt true
    rw [hdaccept]
    rfl
  · exact hdout

end BalancedAssortments.NPStack.Composition
