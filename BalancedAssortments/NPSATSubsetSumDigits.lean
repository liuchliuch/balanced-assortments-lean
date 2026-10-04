import Mathlib

/-! Base-ten packing for the SAT-to-Subset-Sum digit gadget. These lemmas
establish absence of carries and equality coordinate by coordinate. -/
namespace BalancedAssortments.NPSATSubsetSum

def pack {n : ℕ} (digits : Fin n → ℕ) : ℕ := Nat.ofDigits 10 (List.ofFn digits)

@[simp] lemma pack_zero (n : ℕ) : pack (fun _ : Fin n => 0) = 0 := by
  simp [pack,List.ofFn_const]

lemma pack_add {n : ℕ} (a b : Fin n → ℕ) : pack (fun i => a i+b i) = pack a+pack b := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack,List.ofFn_succ,Nat.ofDigits_cons]
    have h := ih (fun i => a i.succ) (fun i => b i.succ)
    unfold pack at h
    rw [h]
    ring

lemma pack_sum {I : Type*} {n : ℕ} (s : Finset I) (d : I → Fin n → ℕ) :
    pack (fun j => ∑ i ∈ s,d i j) = ∑ i ∈ s,pack (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [pack_add,ih]

lemma pack_injective {n : ℕ} (a b : Fin n → ℕ)
    (ha : ∀ i,a i<10) (hb : ∀ i,b i<10) : pack a=pack b ↔ a=b := by
  constructor
  · intro h
    have he : List.ofFn a = List.ofFn b := Nat.ofDigits_inj_of_len_eq (by decide)
      (by simp) (by simpa using ha) (by simpa using hb) h
    exact List.ofFn_inj.mp he
  · rintro rfl; rfl

/-- A finite subset of integer gadget items reaches the packed target exactly
when every digit reaches its target, provided the actual selected digit sums
are below the radix. This does not assume the desired digit equations. -/
theorem subset_packed_iff {I : Type*} {n : ℕ} (s : Finset I) (d : I → Fin n → ℕ)
    (target : Fin n → ℕ) (hselected : ∀ j,(∑ i ∈ s,d i j)<10)
    (htarget : ∀ j,target j<10) :
    (∑ i ∈ s,pack (d i))=pack target ↔ ∀ j,(∑ i ∈ s,d i j)=target j := by
  rw [← pack_sum,pack_injective _ _ hselected htarget]
  exact funext_iff

lemma pack_pos {n : ℕ} (d : Fin n → ℕ) (i : Fin n) (hi : 0<d i) : 0<pack d := by
  have hs : d i ≤ (List.ofFn d).sum := by
    rw [List.sum_ofFn]
    exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hi.trans_le (hs.trans (Nat.sum_le_ofDigits (List.ofFn d) (by decide)))

end BalancedAssortments.NPSATSubsetSum
