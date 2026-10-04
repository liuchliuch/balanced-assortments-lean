import BalancedAssortments.NPStackSourceVerifierTraceSemantics
import BalancedAssortments.NPStackVerifierControlBound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma accumulator_width (s : Registers) {A B : ℕ} (hBA : B≤A)
    (ha : ∀ k,width (s k)≤A)
    (hb : ∀ k∈[RowReg.price,.priceDen,.attraction,.attractionDen,.numerator,.one],width (s k)≤B) :
    ∀ k,width (evalAssignments accumulatorAssignments s k)≤A+6*B+4 := by
  have hp:=hb .price (by simp);have hpd:=hb .priceDen (by simp)
  have hv:=hb .attraction (by simp);have hvd:=hb .attractionDen (by simp)
  have hn:=hb .numerator (by simp);have ho:=hb .one (by simp)
  have hrn:=ha .rankNum;have hrd:=ha .rankDen;have hsn:=ha .revenueNum;have hsd:=ha .revenueDen
  have ht:=ha .total;have hc:=ha .count
  have h1:=zmul_width (s .numerator) (s .attractionDen)
  have h2:=zmul_width (zmul (s .numerator) (s .attractionDen)).1 (s .rankDen)
  have h3:=zmul_width (s .attraction) (s .rankNum)
  have h4:=zadd_width (zmul (s .attraction) (s .rankNum)).1
    (zmul (zmul (s .numerator) (s .attractionDen)).1 (s .rankDen)).1
  have h5:=zmul_width (s .attraction) (s .rankDen)
  have h6:=zmul_width (s .price) (s .numerator)
  have h7:=zmul_width (zmul (s .price) (s .numerator)).1 (s .revenueDen)
  have h8:=zmul_width (s .priceDen) (s .revenueNum)
  have h9:=zadd_width (zmul (s .priceDen) (s .revenueNum)).1
    (zmul (zmul (s .price) (s .numerator)).1 (s .revenueDen)).1
  have h10:=zmul_width (s .priceDen) (s .revenueDen)
  have h11:=zadd_width (s .numerator) (s .total)
  have h12:=zadd_width (s .one) (s .count)
  intro k
  have hk:=ha k
  cases k <;> simp [evalAssignments,accumulatorAssignments,List.foldl_cons,List.foldl_nil,
    evalAssignment,Function.update] <;> omega

lemma accumulator_cap_eq (s : Registers) :
    evalAssignments accumulatorAssignments (evalAssignments capAssignments s)=evalAssignments accumulatorAssignments s := by
  funext k;cases k <;> simp [evalAssignments,capAssignments,accumulatorAssignments,evalAssignment,Function.update]

lemma rowEffect_width (s : Registers) {A B : ℕ} (hBA : B≤A)
    (ha : ∀ k,width (s k)≤A)
    (hb : ∀ k∈[RowReg.price,.priceDen,.attraction,.attractionDen,.numerator,.one],width (s k)≤B) :
    ∀ k,width (VerifierCommands.rowEffect s k)≤A+6*B+5 := by
  have hu := accumulator_width s hBA ha hb
  unfold VerifierCommands.rowEffect
  rw [accumulator_cap_eq]
  let u := evalAssignments accumulatorAssignments s
  intro k
  by_cases hk : k=.maximum
  · subst k
    have hm:=hu .maximum
    have hn:=hu .numerator
    have hz:=hu .zero
    have hnum : u .numerator=s .numerator := accumulatorAssignments_preserves s .numerator (by simp)
    have hzero : u .zero=s .zero := accumulatorAssignments_preserves s .zero (by simp)
    have hN:=ha .numerator;have hZ:=ha .zero
    have hadd:=zadd_width (u .numerator) (u .zero)
    rw [hnum,hzero] at hadd
    change width ((eval VerifierCommands.maxCommand u).2 .maximum)≤_
    simp only [VerifierCommands.maxCommand,eval]
    split_ifs <;> simp [evalAssignments,evalAssignment,Function.update]
    · change width (zadd (u .numerator) (u .zero)).1≤_
      rw [hnum,hzero]
      omega
    · exact hm.trans (by omega)
  · rw [VerifierCommands.maxCommand_preserves _ k hk]
    exact (hu k).trans (by omega)

lemma loadRecord_width (s : Registers) (x : WitnessRecord) {A B : ℕ}
    (hBA : B≤A) (ha : ∀ k,width (s k)≤A) (hx : recordWidth x≤B) :
    ∀ k,width (loadRecord s x k)≤A := by
  unfold recordWidth ComplexityTimeFractions.width at hx
  intro k
  have hk:=ha k
  cases k <;> simp only [loadRecord]
  all_goals first | exact hk | (simp only [width,List.length_nil,Nat.max_zero]; omega) | omega

lemma loadRecord_fresh (s : Registers) (x : WitnessRecord) {B : ℕ}
    (ho : width (s .one)≤B) (hx : recordWidth x≤B) :
    ∀ k∈[RowReg.price,.priceDen,.attraction,.attractionDen,.numerator,.one],width (loadRecord s x k)≤B := by
  unfold recordWidth ComplexityTimeFractions.width at hx
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [loadRecord]
  all_goals first | exact ho | omega | (simp only [width,List.length_nil,Nat.max_zero]; omega)

lemma next_width (s : Registers) (x : WitnessRecord) {A B : ℕ}
    (hBA : B≤A) (ha : ∀ k,width (s k)≤A) (ho : width (s .one)≤B) (hx : recordWidth x≤B) :
    ∀ k,width (nextRegisters s x k)≤A+6*B+5 :=
  rowEffect_width _ hBA (loadRecord_width s x hBA ha hx) (loadRecord_fresh s x ho hx)

theorem trace_width (rows : List InputRow) (s : Registers) (balance : List Bool) {A B : ℕ}
    (hBA : B≤A) (ha : ∀ k,width (s k)≤A) (ho : width (s .one)≤B)
    (hx : ∀ r∈rows,recordWidth r.1≤B) :
    ∀ k,width ((traceEnd rows s balance).1 k)≤A+rows.length*(6*B+5) := by
  induction rows generalizing s balance A with
  | nil => simpa [traceEnd] using ha
  | cons r rows ih =>
    have hn := next_width s r.1 hBA ha ho (hx r (by simp))
    have hon : width (nextRegisters s r.1 .one)≤B := by rw [next_readonly s r.1 .one (by simp)];exact ho
    have hh := ih (nextRegisters s r.1) (nextBalance s r.1 balance) (by omega) hn hon
      (by intro x hh;exact hx x (by simp [hh]))
    intro k
    have hk:=hh k
    simpa [traceEnd,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hk

end BalancedAssortments.NPStack.SourceVerifier
