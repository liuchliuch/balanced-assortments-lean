import BalancedAssortments.NPStackSourceVerifierWidth

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma packed_field_length (s : Registers) (balance : List Bool) {A : ℕ}
    (ha : ∀ k,width (s k)≤A) (i : Fin 9) : (packedStore s [] balance (.inl i)).length≤A := by
  have hp:=ha .price;have hpd:=ha .priceDen;have hv:=ha .attraction
  have hvd:=ha .attractionDen;have hn:=ha .numerator
  simp only [width] at hp hpd hv hvd hn
  fin_cases i <;> simp [packedStore,arithmeticInverse,arithmeticMap,extraStore,
    SignedAssignment.initialStore,SignedAssignment.store,width] <;> omega

lemma emitted_field_length (s : Registers) (balance : List Bool) (active : Bool) {A : ℕ}
    (ha : ∀ k,width (s k)≤A) (i : Fin 9) :
    (emittedRowStore active (packedStore s [] balance) (.inl i)).length≤A := by
  have hi:=packed_field_length s balance ha i
  fin_cases i <;> simpa [emittedRowStore,emittedStore,emitSource,Function.update] using hi

lemma row_clear_bound (s : Registers) (balance : List Bool) (active : Bool) {A : ℕ}
    (ha : ∀ k,width (s k)≤A) :
    ClearRows.clearCost ClearRows.rowKeys (emittedRowStore active (packedStore s [] balance))≤9*(A+1) := by
  apply (ClearRows.clearCost_bound _ _ (B:=A) ?_).trans (by simp [ClearRows.rowKeys])
  intro k hk
  simp only [ClearRows.rowKeys,List.mem_map] at hk
  obtain ⟨i,hi,rfl⟩ := hk
  exact emitted_field_length s balance active ha i

def rowCoefficient : ℕ := costCoefficient (VerifierCommands.rowCommand false)+costCoefficient (VerifierCommands.rowCommand true)
def rowBudget (A B : ℕ) : ℕ := rowCoefficient*(A+1)^2+B+100*(A+6*B+6)

theorem body_row_bounded (s : Registers) (mask balance : List Bool) (active : Bool) {A B : ℕ}
    (hBA : B≤A) (hs : ∀ k,width (s k)≤A)
    (hf : ∀ k∈[RowReg.price,.priceDen,.attraction,.attractionDen,.numerator,.one],width (s k)≤B)
    (hmask : mask.length≤B) (hm : NPStackMask.maskValue mask=some active)
    (ha : (eval (VerifierCommands.rowCommand active) s).1=true) :
    ∃ t≤rowBudget A B, Run bodyProgram t ⟨bodyProgram.start,packedStore s mask balance⟩
      ⟨.inr (ClearRows.clearDone ClearRows.rowKeys),
        NPStackSourcePairing.rowStore (fun _=>[])
          (workspaceStore (VerifierCommands.rowEffect s)
            (NPStackFields.dataFields (balanceRecord active (VerifierCommands.rowEffect s))++balance))⟩ := by
  obtain ⟨t,ht,hr⟩ := inner_row_run s mask balance active hm ha
  have hw:=rowEffect_width s hBA hs hf
  have h7:=packed_field_length _ balance hw 7
  have h8:=packed_field_length _ balance hw 8
  have hc:=row_clear_bound _ balance active hw
  have hbudget:=budget_quadratic (VerifierCommands.rowCommand active) s (L:=A+1) (by intro k;have h:=hs k;omega)
  have hcoef : costCoefficient (VerifierCommands.rowCommand active)≤rowCoefficient := by cases active <;> simp [rowCoefficient]
  have hbound:=Nat.mul_le_mul_right ((A+1)^2) hcoef
  have hh := ClearRows.finish_run innerProgram ClearRows.rowKeys hr (by rfl)
  rw [emitted_row_workspace] at hh
  refine ⟨_,?_,hh⟩
  dsimp only
  unfold rowBudget
  omega

end BalancedAssortments.NPStack.SourceVerifier
