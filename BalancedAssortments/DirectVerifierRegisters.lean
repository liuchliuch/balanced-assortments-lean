import BalancedAssortments.DirectVerifierStream

namespace BalancedAssortments.DirectVerifier
open ComplexityTimeVerifier

/-- Fixed finite register layout for one concrete verifier row body. -/
inductive RowReg
  | price | priceDen | attraction | attractionDen | numerator
  | q | alpha | alphaDen | target | targetDen | capacity | declaredCount
  | rankDen | rankNum | revenueDen | revenueNum | total | maximum
  | term | product | zero | one | count
  deriving DecidableEq, Fintype

inductive ArithmeticAssignment
  | add (dst a b : RowReg)
  | multiply (dst fresh acc : RowReg)
  deriving DecidableEq

/-- Specification of a single primitive assignment. Operational realization is
by the finite SignedAssignment programs, never by this function as an opcode. -/
def evalAssignment (op : ArithmeticAssignment) (s : RowReg→ZBits) : RowReg→ZBits :=
  match op with
  | .add dst a b => Function.update s dst (zadd (s a) (s b)).1
  | .multiply dst a b => Function.update s dst (zmul (s a) (s b)).1

def evalAssignments (ops : List ArithmeticAssignment) (s : RowReg→ZBits) : RowReg→ZBits :=
  ops.foldl (fun s op => evalAssignment op s) s

/-- The literal, fixed-length arithmetic program for both streaming cleared
sums. Fresh record terms are the left multipliers. Destination aliasing is
intentional and is supported by the actual copying assignment primitives. -/
def accumulatorAssignments : List ArithmeticAssignment := [
  .multiply .term .numerator .attractionDen,
  .multiply .product .term .rankDen,
  .multiply .rankNum .attraction .rankNum,
  .add .rankNum .rankNum .product,
  .multiply .rankDen .attraction .rankDen,
  .multiply .term .price .numerator,
  .multiply .product .term .revenueDen,
  .multiply .revenueNum .priceDen .revenueNum,
  .add .revenueNum .revenueNum .product,
  .multiply .revenueDen .priceDen .revenueDen,
  .add .total .numerator .total,
  .add .count .one .count]

def capAssignments : List ArithmeticAssignment := [
  .multiply .term .attractionDen .numerator,
  .multiply .product .attraction .q]

def balanceAssignments : List ArithmeticAssignment := [
  .multiply .term .alpha .maximum,
  .multiply .product .alphaDen .numerator]

def finalAssignments : List ArithmeticAssignment := [
  .multiply .term .capacity .q,
  .multiply .product .term .rankDen]

def revenueAssignments : List ArithmeticAssignment := [
  .multiply .term .target .revenueDen,
  .add .product .q .total,
  .multiply .term .term .product,
  .multiply .product .targetDen .revenueNum]

def registerState (s : RowReg→ZBits) : StreamState :=
  ⟨(s .rankDen,s .rankNum),(s .revenueDen,s .revenueNum),s .total,s .maximum⟩

def HoldsRecord (s : RowReg→ZBits) (x : WitnessRecord) : Prop :=
  s .price=x.price.num ∧ s .priceDen=(x.price.den,[]) ∧
  s .attraction=x.attraction.num ∧ s .attractionDen=(x.attraction.den,[]) ∧ s .numerator=x.numerator

set_option maxRecDepth 4096 in
lemma accumulatorAssignments_correct (s : RowReg→ZBits) (x : WitnessRecord) (hx : HoldsRecord s x) :
    (registerState (evalAssignments accumulatorAssignments s)).rank=(streamStep (registerState s) x).rank ∧
    (registerState (evalAssignments accumulatorAssignments s)).revenue=(streamStep (registerState s) x).revenue ∧
    (registerState (evalAssignments accumulatorAssignments s)).total=(streamStep (registerState s) x).total ∧
    (evalAssignments accumulatorAssignments s) .count=(zadd (s .one) (s .count)).1 ∧
    (evalAssignments accumulatorAssignments s) .maximum=s .maximum := by
  rcases hx with ⟨hr,hrd,hv,hvd,hp⟩
  simp [evalAssignments,accumulatorAssignments,evalAssignment,Function.update,
    registerState,streamStep,recordRankTerm,recordRevenueTerm,sumStepBits,hr,hrd,hv,hvd,hp]

lemma capAssignments_correct (s : RowReg→ZBits) :
    (evalAssignments capAssignments s) .term=(zmul (s .attractionDen) (s .numerator)).1 ∧
    (evalAssignments capAssignments s) .product=(zmul (s .attraction) (s .q)).1 := by
  simp [evalAssignments,capAssignments,evalAssignment,Function.update]
lemma balanceAssignments_correct (s : RowReg→ZBits) :
    (evalAssignments balanceAssignments s) .term=(zmul (s .alpha) (s .maximum)).1 ∧
    (evalAssignments balanceAssignments s) .product=(zmul (s .alphaDen) (s .numerator)).1 := by
  simp [evalAssignments,balanceAssignments,evalAssignment,Function.update]
lemma finalAssignments_correct (s : RowReg→ZBits) :
    (evalAssignments finalAssignments s) .product=(zmul (zmul (s .capacity) (s .q)).1 (s .rankDen)).1 := by
  simp [evalAssignments,finalAssignments,evalAssignment,Function.update]
lemma revenueAssignments_correct (s : RowReg→ZBits) :
    (evalAssignments revenueAssignments s) .term=(zmul (zmul (s .target) (s .revenueDen)).1 (zadd (s .q) (s .total)).1).1 ∧
    (evalAssignments revenueAssignments s) .product=(zmul (s .targetDen) (s .revenueNum)).1 := by
  simp [evalAssignments,revenueAssignments,evalAssignment,Function.update]

lemma accumulatorAssignments_preserves (s : RowReg→ZBits) (k : RowReg)
    (hk : k∈[RowReg.price,.priceDen,.attraction,.attractionDen,.numerator,.q,.alpha,.alphaDen,
      .target,.targetDen,.capacity,.declaredCount,.zero,.one]) :
    (evalAssignments accumulatorAssignments s) k=s k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [evalAssignments,accumulatorAssignments,evalAssignment,Function.update]

end BalancedAssortments.DirectVerifier
