import BalancedAssortments.FixedSupportAmbientCertified

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
variable {I : Type*} [DecidableEq I]

/-- A duplicate-free structural selection carries its own exact indexing of
the prescribed support. The equivalence is proof-side and executes no search. -/
def indexEquiv (A : Finset I) (ids : List I) (hn : ids.Nodup)
    (hm : ∀ i,i∈ids ↔ i∈A) : Fin ids.length≃A :=
  Equiv.ofBijective (fun j=>⟨ids.get j,(hm _).mp (List.get_mem _ _)⟩) (by
    constructor
    · intro a b h
      exact (List.nodup_iff_injective_get.mp hn) (congrArg Subtype.val h)
    · intro i
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp ((hm i).mpr i.property)
      refine ⟨j,?_⟩
      apply Subtype.ext
      exact hj)

@[simp] lemma indexEquiv_apply (A : Finset I) (ids : List I) (hn : ids.Nodup)
    (hm : ∀ i,i∈ids ↔ i∈A) (j : Fin ids.length) : (indexEquiv A ids hn hm j).val=ids.get j := rfl

lemma index_length (A : Finset I) (ids : List I) (hn : ids.Nodup)
    (hm : ∀ i,i∈ids ↔ i∈A) : ids.length=A.card := by
  have h:=Fintype.card_congr (indexEquiv A ids hn hm)
  simpa using h

/-- Canonical indexing of positions selected by the supplied Boolean mask. -/
def selectedIds {N : ℕ} (mask : Fin N→Bool) : List (Fin N) := (List.finRange N).filter mask
lemma selectedIds_nodup {N : ℕ} (mask : Fin N→Bool) : (selectedIds mask).Nodup :=
  (List.nodup_finRange N).filter mask
lemma selectedIds_mem {N : ℕ} (mask : Fin N→Bool) (A : Finset (Fin N))
    (hm : ∀ i,mask i=true ↔ i∈A) (i : Fin N) : i∈selectedIds mask ↔ i∈A := by
  simp [selectedIds,hm]

end BalancedAssortments.FixedSupportAmbient
