import BalancedAssortments.NPStackSourceReject
import BalancedAssortments.NPStackMacroData

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros

def store (wi wo b a tr qu ct pr x y z : List Bool) : Reg → List Bool
  | .wireIn => wi
  | .wireOut => wo
  | .target => b
  | .item => a
  | .triple => tr
  | .quintuple => qu
  | .count => ct
  | .price => pr
  | .temp1 => x
  | .temp2 => y
  | .temp3 => z

@[simp] lemma store_wireIn (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .wireIn=wi := rfl
@[simp] lemma update_store_wireIn (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .wireIn v=store v wo b a tr qu ct pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_wireOut (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .wireOut=wo := rfl
@[simp] lemma update_store_wireOut (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .wireOut v=store wi v b a tr qu ct pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_target (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .target=b := rfl
@[simp] lemma update_store_target (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .target v=store wi wo v a tr qu ct pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_item (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .item=a := rfl
@[simp] lemma update_store_item (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .item v=store wi wo b v tr qu ct pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_triple (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .triple=tr := rfl
@[simp] lemma update_store_triple (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .triple v=store wi wo b a v qu ct pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_quintuple (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .quintuple=qu := rfl
@[simp] lemma update_store_quintuple (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .quintuple v=store wi wo b a tr v ct pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_count (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .count=ct := rfl
@[simp] lemma update_store_count (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .count v=store wi wo b a tr qu v pr x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_price (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .price=pr := rfl
@[simp] lemma update_store_price (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .price v=store wi wo b a tr qu ct v x y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_temp1 (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .temp1=x := rfl
@[simp] lemma update_store_temp1 (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .temp1 v=store wi wo b a tr qu ct pr v y z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_temp2 (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .temp2=y := rfl
@[simp] lemma update_store_temp2 (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .temp2 v=store wi wo b a tr qu ct pr x v z := by
  funext k; cases k <;> simp [store]

@[simp] lemma store_temp3 (wi wo b a tr qu ct pr x y z : List Bool) : store wi wo b a tr qu ct pr x y z .temp3=z := rfl
@[simp] lemma update_store_temp3 (wi wo b a tr qu ct pr x y z v : List Bool) :
    Function.update (store wi wo b a tr qu ct pr x y z) .temp3 v=store wi wo b a tr qu ct pr x y v := by
  funext k; cases k <;> simp [store]

def stable (wi wo b tr qu ct : List Bool) : Reg → List Bool := store wi wo b [] tr qu ct [] [] [] []

lemma push_step (q next : Stage) (r : Reg) (bit : Bool) (s : Reg → List Bool)
    (h : table q=.push r bit next) :
    Step program (cfg q s) (cfg next (Function.update s r (bit::s r))) := by
  simp [Step,successors,program,compile,code,cfg,h]

end BalancedAssortments.NPStackSourceReduction
