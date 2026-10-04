import BalancedAssortments.NPStackVerifierCommands
import BalancedAssortments.NPStackSourcePairingSound
import BalancedAssortments.NPStackMask

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier

inductive Extra | balance | maskFlag | maskPayload | emitScratch
  deriving DecidableEq, Fintype
abbrev Workspace := SignedAssignment.Stack RowReg ⊕ Extra
abbrev BodyStack := Fin 9 ⊕ Workspace
abbrev Stack := NPStackSourcePairing.Stack Workspace

def sourceStack : Stack := .source
def certificateStack : Stack := .certificate

def arithmeticMap : SignedAssignment.Stack RowReg→BodyStack
  | .reg .price false => .inl 0
  | .reg .price true => .inl 1
  | .reg .priceDen false => .inl 2
  | .reg .attraction false => .inl 3
  | .reg .attraction true => .inl 4
  | .reg .attractionDen false => .inl 5
  | .reg .numerator false => .inl 7
  | .reg .numerator true => .inl 8
  | k => .inr (.inl k)

def arithmeticInverse : BodyStack→Option (SignedAssignment.Stack RowReg)
  | .inl i => match i.val with
    | 0 => some (.reg .price false)
    | 1 => some (.reg .price true)
    | 2 => some (.reg .priceDen false)
    | 3 => some (.reg .attraction false)
    | 4 => some (.reg .attraction true)
    | 5 => some (.reg .attractionDen false)
    | 7 => some (.reg .numerator false)
    | 8 => some (.reg .numerator true)
    | _ => none
  | .inr (.inl k) => some k
  | .inr (.inr _) => none

lemma arithmeticMap_inverse (k : SignedAssignment.Stack RowReg) :
    arithmeticInverse (arithmeticMap k)=some k := by
  cases k with
  | reg v n => cases v <;> cases n <;> rfl
  | work k | copyScratch | transferScratch => rfl

lemma arithmeticMap_injective : Function.Injective arithmeticMap := by
  intro a b h
  have hh:=congrArg arithmeticInverse h
  simpa only [arithmeticMap_inverse,Option.some.injEq] using hh

def maskMap : Bool→BodyStack
  | false => .inl 6
  | true => .inr (.inr .maskFlag)
lemma maskMap_injective : Function.Injective maskMap := by
  intro a b h;cases a <;> cases b <;> simp_all [maskMap]

/-- The ten literal header fields occupy stable signed-register components.
Source count/capacity/denominator fields have separately empty negative stacks. -/
def sourceHeader (i : Fin 8) : BodyStack :=
  .inr (.inl (match i.val with
    | 0 => .reg .declaredCount false
    | 1 => .reg .capacity false
    | 2 => .reg .alpha false
    | 3 => .reg .alpha true
    | 4 => .reg .alphaDen false
    | 5 => .reg .target false
    | 6 => .reg .target true
    | _ => .reg .targetDen false))
def certificateHeader (i : Fin 2) : BodyStack := .inr (.inl (.reg .q (decide (i.val=1))))

end BalancedAssortments.NPStack.SourceVerifier
