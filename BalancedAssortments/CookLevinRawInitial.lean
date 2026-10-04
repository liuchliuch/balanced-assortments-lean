import BalancedAssortments.CookLevinRawTransitions

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

def paddedSymbols (word : List Bool) (T : ℕ) : List ℕ :=
  List.replicate T 2 ++ (word.map Bool.toNat ++ List.replicate (T+1) 2)
lemma paddedSymbols_length (word : List Bool) (T : ℕ) :
    (paddedSymbols word T).length=windowWidth word T := by simp [paddedSymbols,windowWidth];omega

lemma paddedSymbols_initial (M : Machine) (word : List Bool) (T : ℕ) :
    paddedSymbols word T=(List.finRange (windowWidth word T)).map (fun p => ((windowInitial M word T).tape p).val) := by
  apply List.ext_getElem
  · simp [paddedSymbols_length]
  · intro i hi hj
    have hbound : i<windowWidth word T := by simpa only [List.length_map,List.length_finRange] using hj
    have hnat : ((i : ℤ)-(T : ℤ)).toNat=i-T := by omega
    simp only [List.getElem_map,List.getElem_finRange,windowInitial,position]
    by_cases hleft : i<T
    · have hneg : ¬0≤(i : ℤ)-(T : ℤ) := by omega
      simp [paddedSymbols,List.getElem_append,hleft,inputTape,hneg,blank,Nat.not_le.mpr hleft]
    · have hnonneg : 0≤(i : ℤ)-(T : ℤ) := by omega
      by_cases hmid : i-T<word.length
      · cases hb : word[i-T] <;> simp [paddedSymbols,List.getElem_append,hleft,hmid,inputTape,hnonneg,hnat,
          List.getElem?_eq_getElem hmid,bitSymbol,Nat.le_of_not_gt hleft,hb]
      · have hnone : word.length ≤ i-T := by omega
        simp [paddedSymbols,List.getElem_append,hleft,hmid,inputTape,hnonneg,hnat,
          List.getElem?_eq_none hnone,blank,Nat.le_of_not_gt hleft]

lemma rawInputCells_initial (M : Machine) (word : List Bool) (clock : List Unit) :
    (rawInputCells word clock).1.map value=(List.finRange (windowWidth word clock.length)).map
      (fun p => ((windowInitial M word clock.length).tape p).val) := by
  rw [rawInputCells_decode,← paddedSymbols_initial M word clock.length]
  simp [paddedSymbols,List.replicate_add,List.append_assoc]

lemma zip_refine {α β γ : Type*} {n : ℕ} (xs : List α) (ys : List β)
    (fx : α → ℕ) (fy : β → ℕ) (target : Fin n → ℕ)
    (hx : xs.map fx=List.range n) (hy : ys.map fy=(List.finRange n).map target)
    (raw : α × β → γ) (spec : Fin n → γ)
    (h : ∀ x∈xs,∀ y∈ys,∀ i : Fin n,fx x=i.val → fy y=target i → raw (x,y)=spec i) :
    (xs.zip ys).map raw=(List.finRange n).map spec := by
  have hxl : xs.length=n := by simpa using congrArg List.length hx
  have hyl : ys.length=n := by simpa using congrArg List.length hy
  apply List.ext_getElem
  · simp [hxl,hyl]
  · intro k hk hk'
    have kn : k<n := by simpa only [List.length_map,List.length_finRange] using hk'
    have kx : k<xs.length := by omega
    have ky : k<ys.length := by omega
    have hxv : fx xs[k]=k := by
      have hh := congrArg (fun l => l[k]?) hx
      simpa [List.getElem?_eq_getElem kx,List.getElem?_range kn] using hh
    have hyv : fy ys[k]=target ⟨k,kn⟩ := by
      have hh := congrArg (fun l => l[k]?) hy
      simpa [List.getElem?_eq_getElem ky,List.getElem?_eq_getElem (show k<(List.finRange n).length by simpa using kn)] using hh
    simp only [List.getElem_map,List.getElem_zip,List.getElem_finRange]
    exact h xs[k] (List.getElem_mem kx) ys[k] (List.getElem_mem ky) ⟨k,kn⟩ hxv hyv

lemma rawInitial_refines (M : Machine) (word : List Bool) (clock : List Unit) {d : RawDimensions}
    (hd : DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) (windowWidth word clock.length)
      clock.length (M.rules.length+1) d)
    (cells : List (List Bool)) (hc : cells.map value=List.range (windowWidth word clock.length)) :
    decodeFormula (rawInitial d (machineConstants M).start cells (rawInputCells word clock).1).1=
      initialFormula M (windowWidth word clock.length) clock.length (windowInitial M word clock.length) := by
  simp only [rawInitial,initialFormula,rawAppend_decode,rawForce_decode]
  rw [stateLabel_refines hd 0 M.start rfl (by simp [machineConstants])]
  have hh := headLabel_refines hd 0 (windowInitial M word clock.length).head (bt := []) (bp := d.t) rfl hd.t_eq
  rw [hh]
  apply congrArg ([[pos (Var.state 0 M.start : TVar M (windowWidth word clock.length) clock.length)]] ++ ·)
  apply congrArg ([[pos (Var.head 0 (windowInitial M word clock.length).head : TVar M (windowWidth word clock.length) clock.length)]] ++ ·)
  rw [rawFlatMap_decode]
  have hz := zip_refine cells (rawInputCells word clock).1 value value
    (fun p => ((windowInitial M word clock.length).tape p).val) hc (rawInputCells_initial M word clock)
    (fun pair => decodeFormula (rawForce (tapeLabel d [] pair.1 pair.2)).1)
    (fun p => force (Var.tape 0 p ((windowInitial M word clock.length).tape p) : TVar M (windowWidth word clock.length) clock.length))
    (by
      intro bp hbp ba hba p hp ha
      dsimp only
      rw [rawForce_decode,tapeLabel_refines hd 0 p ((windowInitial M word clock.length).tape p) rfl hp ha]
      rfl)
  exact congrArg List.flatten hz

end BalancedAssortments.CookLevin
