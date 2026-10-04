import BalancedAssortments.NPStackSourceVerifierLayout
import BalancedAssortments.NPStackVerifierRowSemantics

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def extraStore (mask balance : List Bool) (k : BodyStack) : List Bool :=
  if k=.inl 6 then mask else if k=.inr (.inr .balance) then balance else []

def packedStore (s : Registers) (mask balance : List Bool) (k : BodyStack) : List Bool :=
  match arithmeticInverse k with
  | some a => if arithmeticMap a=k then SignedAssignment.initialStore s a else extraStore mask balance k
  | none => extraStore mask balance k

lemma packed_projection (s : Registers) (mask balance : List Bool) (a : SignedAssignment.Stack RowReg) :
    packedStore s mask balance (arithmeticMap a)=SignedAssignment.initialStore s a := by
  simp [packedStore,arithmeticMap_inverse]

lemma packed_frame (s t : Registers) (mask balance : List Bool) (k : BodyStack)
    (hk : ∀ a,arithmeticMap a≠k) : packedStore s mask balance k=packedStore t mask balance k := by
  unfold packedStore
  cases h : arithmeticInverse k with
  | none => rfl
  | some a => simp [hk a]

@[simp] lemma packed_mask (s : Registers) (mask balance : List Bool) : packedStore s mask balance (.inl 6)=mask := by
  simp [packedStore,arithmeticInverse,extraStore]
@[simp] lemma packed_balance (s : Registers) (mask balance : List Bool) :
    packedStore s mask balance (.inr (.inr .balance))=balance := by simp [packedStore,arithmeticInverse,extraStore]
@[simp] lemma packed_maskFlag (s : Registers) (mask balance : List Bool) :
    packedStore s mask balance (.inr (.inr .maskFlag))=[] := by simp [packedStore,arithmeticInverse,extraStore]
@[simp] lemma packed_maskPayload (s : Registers) (mask balance : List Bool) :
    packedStore s mask balance (.inr (.inr .maskPayload))=[] := by simp [packedStore,arithmeticInverse,extraStore]
@[simp] lemma packed_emitScratch (s : Registers) (mask balance : List Bool) :
    packedStore s mask balance (.inr (.inr .emitScratch))=[] := by simp [packedStore,arithmeticInverse,extraStore]

lemma packed_other_mask (s : Registers) (mask balance : List Bool) (k : BodyStack) (hk : k≠.inl 6) :
    packedStore s mask balance k=packedStore s [] balance k := by
  unfold packedStore
  cases arithmeticInverse k <;> simp [extraStore,hk]

lemma packed_clear_mask (s : Registers) (mask balance : List Bool) :
    Function.update (packedStore s mask balance) (.inl 6) []=packedStore s [] balance := by
  funext k
  by_cases hk : k=.inl 6
  · subst k;simp
  · simpa [Function.update,hk] using packed_other_mask s mask balance k hk

def recordFields (x : WitnessRecord) (mask : List Bool) : Fin 9→List Bool
  | 0 => x.price.num.1 | 1 => x.price.num.2 | 2 => x.price.den
  | 3 => x.attraction.num.1 | 4 => x.attraction.num.2 | 5 => x.attraction.den
  | 6 => mask | 7 => x.numerator.1 | 8 => x.numerator.2

def workspaceStore (s : Registers) (balance : List Bool) (w : Workspace) : List Bool :=
  packedStore s [] balance (.inr w)

lemma packed_record (s : Registers) (x : WitnessRecord) (mask balance : List Bool) (hx : HoldsRecord s x) :
    packedStore s mask balance=NPStackSourcePairing.rowStore (recordFields x mask) (workspaceStore s balance) := by
  rcases hx with ⟨hr,hrd,hv,hvd,hp⟩
  funext k
  cases k with
  | inl i =>
    fin_cases i <;> simp [packedStore,arithmeticInverse,arithmeticMap,extraStore,recordFields,
      NPStackSourcePairing.rowStore,SignedAssignment.initialStore,SignedAssignment.store,hr,hrd,hv,hvd,hp]
  | inr w => exact packed_other_mask s mask balance (.inr w) (by simp)

end BalancedAssortments.NPStack.SourceVerifier
