import BalancedAssortments.FixedSupportAmbientPreprocess
import BalancedAssortments.FixedSupportAmbientIndexedSolver

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open FixedSupportCostPoints FixedSupportAmbientPreprocess

lemma selected_map {I : Type*} (ids : List I) (data : I→Product) (mask : I→Bool) :
    selected (ids.map data) (ids.map mask)=(ids.filter mask).map data := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    dsimp only [selected] at ih
    cases h : mask i <;> simp [selected,h,ih]

lemma selected_ofFn {N : ℕ} (data : Fin N→Product) (mask : Fin N→Bool) :
    selected (List.ofFn data) (List.ofFn mask)=(selectedIds mask).map data := by
  simpa only [List.ofFn_eq_map,selectedIds] using selected_map (List.finRange N) data mask

lemma pairs_ext {I R : Type*} (xs ys : List (I×R))
    (hi : xs.map Prod.fst=ys.map Prod.fst) (hd : xs.map Prod.snd=ys.map Prod.snd) : xs=ys := by
  have hz (zs : List (I×R)) : (zs.map Prod.fst).zip (zs.map Prod.snd)=zs := by induction zs <;> simp_all
  rw [←hz xs,hi,hd,hz]

lemma labelProducts_ofFn (ps : List Product) :
    (labelProducts ps).1=List.ofFn (fun j=>(j,ps.get j)) := by
  apply pairs_ext
  · simp [List.map_ofFn,Function.comp_def,List.ofFn_eq_map]
  · simpa [List.map_ofFn,Function.comp_def] using (labelProducts_data ps).trans (List.ofFn_get ps).symm

lemma indexed_member (ps : List Product) (x : Fin ps.length×Product)
    (hx : x∈(labelProducts ps).1) : x.2=ps.get x.1 := by
  rw [labelProducts_ofFn] at hx
  obtain ⟨j,hj⟩:=List.mem_ofFn.mp hx
  cases hj
  rfl

lemma get_of_map {I R : Type*} (xs : List R) (ys : List I) (f : I→R)
    (h : xs=ys.map f) (i : Fin xs.length) :
    xs.get i=f (ys.get ⟨i.val,by simpa [h] using i.isLt⟩) := by
  subst xs
  simp

/-- Structural filtering/reindexing produces exactly the selected ambient
products, with a proved bijection from output positions to the prescribed set. -/
theorem prepared_restriction {N : ℕ} (data : Fin N→Product) (mask : Fin N→Bool)
    (A : Finset (Fin N)) (hm : ∀ i,mask i=true ↔ i∈A) (out : Prepared)
    (hp : (prepare (List.ofFn data) (List.ofFn mask)).1=some out) :
    ∃ e : Fin out.products.length≃A,∀ x∈out.indexed,x.2=data (e x.1) := by
  have hc:=prepare_correct hp
  have he : out.products=(selectedIds mask).map data := hc.2.1.trans (selected_ofFn data mask)
  have hl : out.products.length=(selectedIds mask).length := by simp [he]
  let e : Fin out.products.length≃A :=
    (Fin.castOrderIso hl).toEquiv.trans (indexEquiv A (selectedIds mask) (selectedIds_nodup mask) (selectedIds_mem mask A hm))
  refine ⟨e,?_⟩
  intro x hx
  have hi := indexed_member out.products x (by simpa only [hc.2.2.2.1] using hx)
  rw [hi,get_of_map out.products (selectedIds mask) data he x.1]
  rfl

theorem prepare_ofFn {N : ℕ} (data : Fin N→Product) (mask : Fin N→Bool) :
    ∃ out,(prepare (List.ofFn data) (List.ofFn mask)).1=some out := by
  have hs : (selectProducts (List.ofFn data) (List.ofFn mask)).1=
      some (selected (List.ofFn data) (List.ofFn mask)) := by
    rw [selectProducts_correct]
    simp
  simp [prepare,hs]

lemma prepared_valid {N : ℕ} (data : Fin N→Product) (mask : Fin N→Bool) (out : Prepared)
    (hp : (prepare (List.ofFn data) (List.ofFn mask)).1=some out) (hd : ∀ i,(data i).Valid) :
    ∀ p∈out.indexed,p.2.Valid := by
  have hc:=prepare_correct hp
  intro p hp
  have hm : p.2∈out.products := by
    have hh : p.2∈out.indexed.map Prod.snd := List.mem_map.mpr ⟨p,hp,rfl⟩
    rw [hc.2.2.2.2.2] at hh
    exact hh
  have ha := hc.2.2.1.subset hm
  obtain ⟨i,hi⟩:=List.mem_ofFn.mp ha
  rw [←hi]
  exact hd i

end BalancedAssortments.FixedSupportAmbient
