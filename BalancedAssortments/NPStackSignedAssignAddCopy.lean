import BalancedAssortments.NPStackSignedAssignAddCalls

namespace BalancedAssortments.NPStack.SignedAssignAdd
open NPStack ComplexityTimeVerifier SignedAssignment
variable {V : Type*} [DecidableEq V]
set_option maxHeartbeats 1500000

def copyCost (x y : ZBits) : ℕ := 5*(x.1.length+x.2.length+y.1.length+y.2.length)+12

lemma copy_operands_run (a b dst : V) (s : V→ZBits) :
    Run (program a b dst) (copyCost (s a) (s b))
      ⟨.copy .xp .readSource,initialStore s⟩
      ⟨.multiply (.copy false .readSource),store s (signedMulInitial (s a) (s b)) [] []⟩ := by
  let s0 := initialStore s
  let s1 := Function.update s0 (.work .xp) (s a).1
  let s2 := Function.update s1 (.work .xn) (s a).2
  let s3 := Function.update s2 (.work .yp) (s b).1
  let s4 := Function.update s3 (.work .yn) (s b).2
  have h1 := copy_run a b dst .xp s0 (by rfl) (by rfl)
  have h2 := copy_run a b dst .xn s1
    (by simp [s1,s0,initialStore,store,Function.update])
    (by simp [s1,s0,initialStore,store,Function.update,operandWork])
  have h3 := copy_run a b dst .yp s2
    (by simp [s2,s1,s0,initialStore,store,Function.update])
    (by simp [s2,s1,s0,initialStore,store,Function.update,operandWork])
  have h4 := copy_run a b dst .yn s3
    (by simp [s3,s2,s1,s0,initialStore,store,Function.update])
    (by simp [s3,s2,s1,s0,initialStore,store,Function.update,operandWork])
  have hs0 : s0 (sourceReg a b .xp)=(s a).1 := rfl
  have hs1 : s1 (sourceReg a b .xn)=(s a).2 := by
    simp [s1,s0,sourceReg,operandVariable,operandSign,initialStore,store,Function.update]
  have hs2 : s2 (sourceReg a b .yp)=(s b).1 := by
    simp [s2,s1,s0,sourceReg,operandVariable,operandSign,initialStore,store,Function.update]
  have hs3 : s3 (sourceReg a b .yn)=(s b).2 := by
    simp [s3,s2,s1,s0,sourceReg,operandVariable,operandSign,initialStore,store,Function.update]
  rw [hs0] at h1
  rw [hs1] at h2
  rw [hs2] at h3
  rw [hs3] at h4
  have h12 := (h1.trans (Run.one (copy_return a b dst .xp s1))).trans h2
  have h123 := (h12.trans (Run.one (copy_return a b dst .xn s2))).trans h3
  have h1234 := (h123.trans (Run.one (copy_return a b dst .yp s3))).trans h4
  have hall := h1234.trans (Run.one (copy_return a b dst .yn s4))
  have he : s4=store s (signedMulInitial (s a) (s b)) [] [] := by
    funext k
    cases k with
    | reg v n => simp [s4,s3,s2,s1,s0,initialStore,store,Function.update]
    | work k => cases k <;> simp [s4,s3,s2,s1,s0,initialStore,store,signedMulInitial,Function.update]
    | copyScratch | transferScratch => simp [s4,s3,s2,s1,s0,initialStore,store,Function.update]
  rw [he] at hall
  convert hall using 1 <;> dsimp [copyCost] <;> omega


end BalancedAssortments.NPStack.SignedAssignAdd
