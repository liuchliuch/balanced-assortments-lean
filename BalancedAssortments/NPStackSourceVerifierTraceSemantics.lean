import BalancedAssortments.NPStackSourceVerifierTraceSound
import BalancedAssortments.NPStackVerifierFinalSemantics

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def Represents (s : Registers) (a : StreamState) : Prop :=
  (registerState s).rank=a.rank ∧ (registerState s).revenue=a.revenue ∧
  (registerState s).total=a.total ∧ zvalue (s .maximum)=zvalue a.maximum

lemma next_readonly (s : Registers) (x : WitnessRecord) (k : RowReg)
    (hk : k∈[RowReg.q,.alpha,.alphaDen,.target,.targetDen,.capacity,.declaredCount,.zero,.one]) :
    nextRegisters s x k=s k := by
  rw [nextRegisters,rowEffect_readonly _ k (by simp_all)]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

lemma next_represents (s : Registers) (a : StreamState) (x : WitnessRecord)
    (h : Represents s a) (hz : s .zero=zzero) (ho : s .one=zOne) :
    Represents (nextRegisters s x) (streamStep a x) ∧
      zvalue (nextRegisters s x .count)=zvalue (s .count)+1 := by
  have hh := VerifierCommands.rowEffect_spec (loadRecord s x) x (loadRecord_holds s x)
    (by simpa [loadRecord] using hz) (by simpa [loadRecord] using ho)
  have he : registerState (loadRecord s x)=registerState s := rfl
  rw [he] at hh
  rcases h with ⟨hr,hv,ht,hm⟩
  refine ⟨⟨?_,?_,?_,?_⟩,hh.2.2.2.2⟩
  · exact hh.1.trans (by simp only [streamStep,hr])
  · exact hh.2.1.trans (by simp only [streamStep,hv])
  · exact hh.2.2.1.trans (by simp only [streamStep,ht])
  · dsimp only [nextRegisters]
    rw [hh.2.2.2.1]
    simpa only [loadRecord,streamStep,maxBits_value] using congrArg (fun m=>max m (zvalue x.numerator)) hm

lemma trace_readonly (rows : List InputRow) (s : Registers) (balance : List Bool) (k : RowReg)
    (hk : k∈[RowReg.q,.alpha,.alphaDen,.target,.targetDen,.capacity,.declaredCount,.zero,.one]) :
    (traceEnd rows s balance).1 k=s k := by
  induction rows generalizing s balance with
  | nil => rfl
  | cons r rs ih => exact (ih _ _).trans (next_readonly s r.1 k hk)

theorem trace_represents (rows : List InputRow) (s : Registers) (balance : List Bool) (a : StreamState)
    (h : Represents s a) (hz : s .zero=zzero) (ho : s .one=zOne) :
    Represents (traceEnd rows s balance).1 (streamFold (rows.map Prod.fst) a) ∧
      zvalue ((traceEnd rows s balance).1 .count)=zvalue (s .count)+rows.length := by
  induction rows generalizing s balance a with
  | nil => exact ⟨h,by simp [traceEnd]⟩
  | cons r rows ih =>
    obtain ⟨hh,hc⟩ := next_represents s a r.1 h hz ho
    have hz' := (next_readonly s r.1 .zero (by simp)).trans hz
    have ho' := (next_readonly s r.1 .one (by simp)).trans ho
    obtain ⟨hrep,hcount⟩ := ih (nextRegisters s r.1) (nextBalance s r.1 balance) (streamStep a r.1) hh hz' ho'
    refine ⟨hrep,?_⟩
    simp only [traceEnd,List.length_cons,Int.natCast_add,Int.natCast_one]
    rw [hcount,hc]
    ring

end BalancedAssortments.NPStack.SourceVerifier
