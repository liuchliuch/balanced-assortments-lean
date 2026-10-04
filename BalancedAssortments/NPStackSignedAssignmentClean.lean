import BalancedAssortments.NPStackSignedAssignmentCopy

namespace BalancedAssortments.NPStack.SignedAssignment
open NPStack ComplexityTimeVerifier
variable {V : Type*} [DecidableEq V]
set_option maxHeartbeats 1500000

lemma clearDest_pair_run (a b dst : V) (s : V→ZBits) (w : SignedMulStack→List Bool) (c tr : List Bool) :
    Run (program a b dst) ((s dst).1.length+(s dst).2.length+2)
      ⟨.clearDest false,store s w c tr⟩
      ⟨.clearFactor false,store (Function.update s dst ([],[])) w c tr⟩ := by
  let s0 := store s w c tr
  let s1 := Function.update s0 (.reg dst false) []
  let s2 := Function.update s1 (.reg dst true) []
  have h1 := clearDest_run a b dst false s0
  have h2 := clearDest_run a b dst true s1
  have hv : s1 (.reg dst true)=(s dst).2 := by simp [s1,s0,store,Function.update]
  rw [hv] at h2
  have h := h1.trans h2
  have he : s2=store (Function.update s dst ([],[])) w c tr := by
    funext k
    cases k with
    | reg v n => by_cases hv : v=dst <;> cases n <;> simp [s2,s1,s0,store,Function.update,hv]
    | work k | copyScratch | transferScratch => simp [s2,s1,s0,store,Function.update]
  change s2=_ at he
  change Run _ _ _ ⟨_,s2⟩ at h
  rw [he] at h
  convert h using 1 <;> dsimp [s0,store] <;> omega

lemma clearFactor_pair_run (a b dst : V) (s : V→ZBits) (y z : ZBits) :
    Run (program a b dst) (y.1.length+y.2.length+2)
      ⟨.clearFactor false,store s (signedMulFinal y z) [] []⟩
      ⟨.move false false .read,store s (signedMulFinal ([],[]) z) [] []⟩ := by
  let s0 := store s (signedMulFinal y z) [] []
  let s1 := Function.update s0 (.work .yp) []
  let s2 := Function.update s1 (.work .yn) []
  have h1 := clearFactor_run a b dst false s0
  have h2 := clearFactor_run a b dst true s1
  have hv : s1 (.work (factorWork true))=y.2 := by simp [s1,s0,store,signedMulFinal,factorWork,Function.update]
  rw [hv] at h2
  have h := h1.trans h2
  have he : s2=store s (signedMulFinal ([],[]) z) [] [] := by
    funext k
    cases k with
    | work k => cases k <;> simp [s2,s1,s0,store,signedMulFinal,Function.update]
    | reg v n | copyScratch | transferScratch => simp [s2,s1,s0,store,Function.update]
  change Run _ _ _ ⟨_,s2⟩ at h
  rw [he] at h
  convert h using 1 <;> dsimp [s0,store,signedMulFinal,factorWork] <;> omega

lemma move_component_run (a b dst : V) (n : Bool) (s : Stack V→List Bool)
    (hscratch : s .transferScratch=[]) (htarget : s (.reg dst n)=[]) :
    Run (program a b dst) (4*(s (.work (outputWork n))).length+4)
      ⟨.move n false .read,s⟩
      ⟨moveNext n true,Function.update (Function.update s (.work (outputWork n)) []) (.reg dst n)
        (s (.work (outputWork n)))⟩ := by
  let bits := s (.work (outputWork n))
  let s1 := Function.update (Function.update s (.work (outputWork n)) []) .transferScratch bits.reverse
  let s2 := Function.update (Function.update s1 .transferScratch []) (.reg dst n) bits
  have h1 := move_run a b dst n false s
  simp only [moveSource,moveTarget,Bool.false_eq_true,↓reduceIte,hscratch,List.append_nil] at h1
  have hs1 : s1 .transferScratch=bits.reverse := by simp [s1]
  have ht1 : s1 (.reg dst n)=[] := by simp [s1,Function.update,htarget]
  have h2 := move_run a b dst n true s1
  simp [moveSource,moveTarget,hs1,ht1] at h2
  have h := ((h1.trans (Run.one (move_return a b dst n false s1))).trans h2).trans
    (Run.one (move_return a b dst n true s2))
  have he : s2=Function.update (Function.update s (.work (outputWork n)) []) (.reg dst n) bits := by
    funext k
    by_cases hk : k=Stack.transferScratch
    · subst k; simp [s2,s1,Function.update,hscratch]
    · simp [s2,s1,Function.update,hk]
  change Run _ _ _ ⟨_,s2⟩ at h
  rw [he] at h
  dsimp only [bits] at h
  convert h using 1 <;> omega

lemma move_pair_run (a b dst : V) (s : V→ZBits) (z : ZBits) (hzero : s dst=([],[])) :
    Run (program a b dst) (4*(z.1.length+z.2.length)+8)
      ⟨.move false false .read,store s (signedMulFinal ([],[]) z) [] []⟩
      ⟨.done,initialStore (Function.update s dst z)⟩ := by
  let s0 := store s (signedMulFinal ([],[]) z) [] []
  let s1 := Function.update (Function.update s0 (.work .positive) []) (.reg dst false) z.1
  let s2 := Function.update (Function.update s1 (.work .negative) []) (.reg dst true) z.2
  have h1 := move_component_run a b dst false s0 (by rfl) (by simp [s0,store,hzero])
  have hs1 : s1 .transferScratch=[] := by simp [s1,s0,store,Function.update]
  have ht1 : s1 (.reg dst true)=[] := by simp [s1,s0,store,Function.update,hzero]
  have hv1 : s0 (.work (outputWork false))=z.1 := rfl
  rw [hv1] at h1
  have h2 := move_component_run a b dst true s1 hs1 ht1
  have hv2 : s1 (.work (outputWork true))=z.2 := by simp [s1,s0,store,signedMulFinal,outputWork,Function.update]
  rw [hv2] at h2
  have h := h1.trans h2
  have he : s2=initialStore (Function.update s dst z) := by
    funext k
    cases k with
    | reg v n => by_cases hv : v=dst <;> cases n <;> simp [s2,s1,s0,initialStore,store,Function.update,hv]
    | work k => cases k <;> simp [s2,s1,s0,initialStore,store,signedMulFinal,Function.update]
    | copyScratch | transferScratch => simp [s2,s1,s0,initialStore,store,Function.update]
  change Run _ _ _ ⟨_,s2⟩ at h
  rw [he] at h
  convert h using 1 <;> omega

end BalancedAssortments.NPStack.SignedAssignment
