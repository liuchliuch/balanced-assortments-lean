import BalancedAssortments.NPStackSourceBounds

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros

/-- A malformed raw field takes the actual rejecting parser computation, then
returns to the fixed-no emitter. Partial parser scratch is harmless. -/
theorem read_failure (q yes : Stage) (s : Reg → List Bool)
    (hm : table q=.read .wireIn .temp3 .temp2 .temp1 yes .badClear)
    (h1 : s .temp1=[]) (h2 : s .temp2=[]) (h3 : s .temp3=[])
    (hp : (EncodingTime.parseField (s .wireIn)).1=none) :
    ∃ t≤7*(s .wireIn).length+5,∃ after,
      Run program t (cfg q s) (cfg .badClear after) ∧ after .wireOut=s .wireOut := by
  obtain ⟨t,ht,c,hr,hc⟩ := NPStackField.parseField_reject (s .wireIn) hp
  rw [NPStackField.initial_cfg] at hr
  have hmap : Function.Injective (readMap Reg.wireIn Reg.temp3 Reg.temp2 Reg.temp1) := by
    intro x y h;cases x <;> cases y <;> simp_all [readMap]
  have hbefore : Relocated (readMap Reg.wireIn Reg.temp3 Reg.temp2 Reg.temp1)
      (fun st => Label.local q (.read st)) (NPStackField.cfg .header (s .wireIn) [] [] [])
      (⟨Label.local q (.read .header),s⟩ : Config Reg (Label Stage)) := by
    constructor
    · rfl
    · intro k;cases k <;> simp [readMap,NPStackField.cfg,h1,h2,h3]
  obtain ⟨d,hd,hrel,hframe⟩ := hr.relocate (readMap Reg.wireIn Reg.temp3 Reg.temp2 Reg.temp1)
    (fun st => Label.local q (.read st)) hmap (read_extends table .readTarget .wireIn .wireOut hm) hbefore
  have hpc : c.pc=NPStackField.State.reject := by
    cases he : c.pc <;> simp_all [NPStackField.program]
  have hentry : Step program (cfg q s) ⟨Label.local q (.read .header),s⟩ := by
    simp [Step,successors,program,compile,code,cfg,hm]
  have hexit : Step program d (cfg .badClear d.stk) := by
    have he : program.code d.pc=.jump (.main .badClear) := by
      rw [hrel.1,hpc]
      simp [program,compile,code,hm,returnCode,NPStackField.program]
    simp [Step,successors,he,cfg]
  refine ⟨t+2,by omega,d.stk,?_,?_⟩
  · convert Run.succ hentry (hd.trans (Run.one hexit)) using 1 <;> omega
  · exact hframe .wireOut (by intro k;cases k <;> simp [readMap])

end BalancedAssortments.NPStackSourceReduction
