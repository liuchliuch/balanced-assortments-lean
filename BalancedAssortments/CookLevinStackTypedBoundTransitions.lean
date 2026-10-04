import BalancedAssortments.CookLevinStackTypedBoundFamilies

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

lemma choice_const_bounded {M : Machine} {W T : ℕ} {e} (hd : Dimensions M W T e)
    (ht : value (e 5)<T) (j : ℕ) (hj : j<M.rules.length+1) :
    denote e (choice (x 5) (c j))<V M W T := choice_bound hd _ _ ht (by simpa using hj)

lemma rule_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T) (hf : (f 13).length=W)
    (j : ℕ) (hj : j<M.rules.length) (r : Rule M.stateExtra M.symbolExtra) :
    fbounded (V M W T) (Typed.ruleBody M j r) e f := by
  have hg := choice_const_bounded hd ht (j+1) (by omega)
  have hs := state_bound hd (x 5) (c r.source.val) (by simpa using Nat.lt_succ_of_lt ht) (by simpa using r.source.isLt)
  have htarg := state_bound hd (succ (x 5)) (c r.target.val) (by simp;omega) (by simpa using r.target.isLt)
  simp only [Typed.ruleBody,fbounded_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  refine ⟨?_,?_,?_,?_⟩
  · simpa using And.intro hg hs
  · simpa using And.intro hg htarg
  · rw [fbounded_loop]
    intro p
    let u := Function.update e 6 (StackCount.counterBits p.val)
    have hu : Dimensions M W T u := hd.update 6 (by decide) _
    have hut : value (u 5)<T := by simpa [u,Function.update] using ht
    have hup : value (u 6)<W := by simp [u,StackCount.counterBits_value];simpa [hf] using p.isLt
    have hgu := choice_const_bounded hu hut (j+1) (by omega)
    have hhu := head_bound hu (x 5) (x 6) (by simp;omega) hup
    have hru := tape_bound hu (x 5) (x 6) (c r.read.val) (by simp;omega) hup (by simpa using r.read.isLt)
    have hwu := tape_bound hu (succ (x 5)) (x 6) (c r.write.val) (by simp;omega) hup (by simpa using r.write.isLt)
    change fbounded _ _ u f
    simp only [fbounded_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨?_,?_,?_⟩
    · simpa using And.intro hgu (And.intro hhu hru)
    · simpa using And.intro hgu (And.intro hhu hwu)
    · simp only [Typed.dynamicClause,fbounded_clause,cbounded_seq]
      constructor
      · rw [cbounded_cloop]
        intro q
        apply move_bounded (hu.update 8 (by decide) _)
        · simpa [Function.update] using hut
        · simp [StackCount.counterBits_value];simpa [hf] using q.isLt
      · simpa using And.intro hgu hhu
  · rw [fbounded_loop]
    intro p
    let u := Function.update e 6 (StackCount.counterBits p.val)
    have hu : Dimensions M W T u := hd.update 6 (by decide) _
    have hut : value (u 5)<T := by simpa [u,Function.update] using ht
    have hup : value (u 6)<W := by simp [u,StackCount.counterBits_value];simpa [hf] using p.isLt
    change fbounded _ _ u f
    rw [fbounded_all]
    intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    have has : a<M.symbolExtra+3 := List.mem_range.mp ha
    have hgu := choice_const_bounded hu hut (j+1) (by omega)
    have hhu := head_bound hu (x 5) (x 6) (by simp;omega) hup
    have htu := tape_bound hu (x 5) (x 6) (StackTableau.c a) (by simp;omega) hup (by simpa using has)
    have hnu := tape_bound hu (succ (x 5)) (x 6) (StackTableau.c a) (by simp;omega) hup (by simpa using has)
    simpa using And.intro hgu (And.intro hhu (And.intro htu hnu))

lemma halt_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T) (hf : (f 13).length=W) :
    fbounded (V M W T) (Typed.haltBody M) e f := by
  have hg := choice_const_bounded hd ht 0 (by omega)
  simp only [Typed.haltBody,fbounded_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  refine ⟨?_,?_,?_,?_⟩
  · rw [fbounded_typed_clause]
    intro l hl
    rcases List.mem_cons.mp hl with rfl|hl
    · exact hg
    · exact accepting_bounded hd (x 5) (by simp;omega) l hl
  · intro p hp
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
    have hss : s<M.stateExtra+1 := List.mem_range.mp hs
    have hcur := state_bound hd (x 5) (c s) (by simp;omega) (by simpa using hss)
    have hnxt := state_bound hd (succ (x 5)) (c s) (by simp;omega) (by simpa using hss)
    simpa using And.intro hg (And.intro hcur hnxt)
  · rw [fbounded_loop]
    intro p
    let u := Function.update e 6 (StackCount.counterBits p.val)
    have hu : Dimensions M W T u := hd.update 6 (by decide) _
    have hut : value (u 5)<T := by simpa [u,Function.update] using ht
    have hup : value (u 6)<W := by simp [u,StackCount.counterBits_value];simpa [hf] using p.isLt
    have hgu := choice_const_bounded hu hut 0 (by omega)
    have hcur := head_bound hu (x 5) (x 6) (by simp;omega) hup
    have hnxt := head_bound hu (succ (x 5)) (x 6) (by simp;omega) hup
    change fbounded _ _ u f
    simpa using And.intro hgu (And.intro hcur hnxt)
  · rw [fbounded_loop]
    intro p
    let u := Function.update e 6 (StackCount.counterBits p.val)
    have hu : Dimensions M W T u := hd.update 6 (by decide) _
    have hut : value (u 5)<T := by simpa [u,Function.update] using ht
    have hup : value (u 6)<W := by simp [u,StackCount.counterBits_value];simpa [hf] using p.isLt
    change fbounded _ _ u f
    rw [fbounded_all]
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    have has : a<M.symbolExtra+3 := List.mem_range.mp ha
    have hgu := choice_const_bounded hu hut 0 (by omega)
    have hcur := tape_bound hu (x 5) (x 6) (c a) (by simp;omega) hup (by simpa using has)
    have hnxt := tape_bound hu (succ (x 5)) (x 6) (c a) (by simp;omega) hup (by simpa using has)
    simpa using And.intro hgu (And.intro hcur hnxt)

theorem transitions_bounded (M : Machine) (word : List Bool) (T : ℕ) :
    fbounded (tableauVariableCount M word.length T) (Typed.transitions M)
      (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) := by
  simp only [Typed.transitions,fbounded_loop]
  intro t
  let e := Function.update (StackInitialize.scalarEnv M word T) 5 (StackCount.counterBits t.val)
  have hd : Dimensions M (windowWidth word T) T e := (dimensions_scalar M word T).update 5 (by decide) _
  have ht : value (e 5)<T := by simp [e,StackCount.counterBits_value];simpa using t.isLt
  change fbounded _ _ e _
  rw [fbounded_seq]
  constructor
  · exact halt_bounded hd ht (by simp [windowWidth])
  · rw [fbounded_all]
    intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    apply rule_bounded hd ht (by simp [windowWidth]) r.2
    simpa using List.snd_lt_of_mem_zipIdx hr

end BalancedAssortments.CookLevin.StackTableau
