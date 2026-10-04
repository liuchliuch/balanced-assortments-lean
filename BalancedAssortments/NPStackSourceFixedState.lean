import BalancedAssortments.NPStackSourceFixedGuard
import BalancedAssortments.NPStackSourceVerifierSound

namespace BalancedAssortments.NPStack.SourceVerifier.Fixed
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma afterRevenue_eq (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord) :
    Whole.afterRevenue (Whole.scalarStart s c rs)=finalRegisters (Whole.rowEnd s c rs).1 := by
  simp only [Whole.afterRevenue,Whole.afterRank,Whole.afterHeader,Whole.header_state,Whole.scalarStart,finalRegisters]

lemma finish_readonly (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    {u : Registers} (hu : Balance.loopValue (Whole.afterRevenue (Whole.scalarStart s c rs)) (Whole.balanceTriples rs)=some u)
    (k : RowReg) (hk : k∈[RowReg.capacity,.alpha,.alphaDen,.one]) :
    Whole.cleanRegisters u k=Whole.initialRegisters s c k := by
  have hc : Whole.cleanRegisters u k=u k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> rfl
  rw [hc,Balance.loopValue_preserves _ _ _ hu k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> simp [Balance.modifiedRegisters]),afterRevenue_eq]
  rw [final_readonly _ k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> simp)]
  exact trace_readonly _ _ _ k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> simp)

lemma finish_one (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    {u : Registers} (hu : Balance.loopValue (Whole.afterRevenue (Whole.scalarStart s c rs)) (Whole.balanceTriples rs)=some u) :
    zvalue (Whole.cleanRegisters u .one)=1 := by
  rw [finish_readonly s c rs hu .one (by simp)]
  exact zOne_value

lemma finish_store (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    {u : Registers} (hu : Balance.loopValue (Whole.afterRevenue (Whole.scalarStart s c rs)) (Whole.balanceTriples rs)=some u) :
    Header.store [] [] (Balance.stable u [])=Whole.globalStore (Whole.cleanRegisters u) [] := by
  have hc : Whole.Clean (Whole.afterRevenue (Whole.scalarStart s c rs)) := by
    apply Whole.revenue_clean
    apply Whole.rank_clean
    rw [Whole.afterHeader,Whole.header_state]
    exact Whole.cleanRegisters_clean _
  have hd := Balance.loopValue_denominators _ _ _ hu
  have hp : (u .priceDen).2=[] := by rw [hd.1,hc.2.1];rfl
  have hv : (u .attractionDen).2=[] := by rw [hd.2,hc.2.2.2.1];rfl
  unfold Whole.globalStore
  rw [Whole.packed_clean u [] hp hv]
  rfl

open ComplexityTimeSourceParsing ComplexityTimeFractions ComplexityTimeBinary

lemma fraction_one_iff (x : ZBits) (d : List Bool) (hd : 0<value d) :
    decode ⟨x,d⟩=1 ↔ zvalue x=(value d : ℤ) := by
  have hn : (value d : ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  change (zvalue x : ℚ)/(value d : ℚ)=1 ↔ _
  rw [div_eq_one_iff_eq hn]
  constructor <;> intro h <;> exact_mod_cast h

/-- The final physical state retains the exact raw header, so the appended
finite guard recognizes the numeric restriction on the same parsed source. -/
theorem whole_final_guard (word : List Bool) (fields : List (List Bool)) (candidate : List Bool)
    {T : ℕ} {out : Config SourceVerifier.Stack (Whole.State Balance.LoopState)}
    (hp : (EncodingTime.parse word).1=some fields)
    (hr : Run Whole.concreteProgram T (Framing.bodyInput Whole.concreteProgram fields candidate) out)
    (ha : accepts Whole.concreteProgram out) :
    ∃ registers,out.stk=Whole.globalStore registers [] ∧
      ((eval command registers).1=true ↔ FixedParameters word) := by
  obtain ⟨sh,ch,rs,hs,hc,hrows,hh,hrank,hrev,u,hu,hout⟩ :=
    Whole.accepted_conditions_full (NPStackFields.dataFields fields) candidate hr ha
  have hfields := Whole.dataFields_injective hs
  have hparse : (parseSource word).1=some (parsedSource sh rs) := by
    have hpack : (packSource fields).1=some (parsedSource sh rs) := by
      rw [hfields];exact packSource_records sh rs
    simp [parseSource,hp,hpack]
  obtain ⟨s,hps,hlegal,_⟩ := concrete_source_sound word fields candidate hp hr ha
  have heq : s=parsedSource sh rs := Option.some.inj (hps.symm.trans hparse)
  subst s
  have hd : 0<value (sh 4) := hlegal.2.2.2.2.1.1
  refine ⟨Whole.cleanRegisters u,hout.trans (finish_store sh ch rs hu),?_⟩
  rw [command_accepts _ (finish_one sh ch rs hu)]
  rw [finish_readonly sh ch rs hu .capacity (by simp),finish_readonly sh ch rs hu .alpha (by simp),
    finish_readonly sh ch rs hu .alphaDen (by simp)]
  change zvalue (sh 1,[])=2 ∧ zvalue (sh 2,sh 3)=zvalue (sh 4,[]) ↔ _
  rw [show zvalue (sh 1,[])=(value (sh 1) : ℤ) from unsigned_value _,
    show zvalue (sh 4,[])=(value (sh 4) : ℤ) from unsigned_value _]
  constructor
  · rintro ⟨hk,ha⟩
    refine ⟨parsedSource sh rs,hparse,?_,?_⟩
    · change value (sh 1)=2;exact_mod_cast hk
    · exact (fraction_one_iff (sh 2,sh 3) (sh 4) hd).mpr ha
  · rintro ⟨s,hps,hk,ha⟩
    have he : s=parsedSource sh rs := Option.some.inj (hps.symm.trans hparse)
    subst s
    constructor
    · change value (sh 1)=2 at hk;exact_mod_cast hk
    · exact (fraction_one_iff (sh 2,sh 3) (sh 4) hd).mp ha

end BalancedAssortments.NPStack.SourceVerifier.Fixed
