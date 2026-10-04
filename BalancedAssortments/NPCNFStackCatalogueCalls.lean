import BalancedAssortments.NPCNFStackCatalogueProgram
import BalancedAssortments.NPStackMacroData

namespace BalancedAssortments.NPCNF.StackCatalogue
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary

lemma read_tag_call (bits rest m cat : List Bool) :
    Run program (5*bits.length+4)
      (cfg .readTag (store (tagBits bits++false::rest) m [] [] [] cat [] [] []))
      (cfg .inspectTag (store rest m [] [] bits cat [] [] [])) := by
  have h := outer_run (taggedRead_call macroCode .readTag input fresh (q:=.readTag)
    rfl (by decide) (by decide) (by decide) (store (tagBits bits++false::rest) m [] [] [] cat [] [] []) bits rest rfl rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,input,tag]
  | inr r => cases r <;> simp [store,input,tag]

lemma read_label_call (bits rest m cat : List Bool) :
    Run program (5*bits.length+4)
      (cfg .readLabel (store (tagBits bits++false::rest) m [] [] [] cat [] [] []))
      (cfg .invokeMember (store rest m [] bits [] cat [] [] [])) := by
  have h := outer_run (taggedRead_call macroCode .readTag input fresh (q:=.readLabel)
    rfl (by decide) (by decide) (by decide) (store (tagBits bits++false::rest) m [] [] [] cat [] [] []) bits rest rfl rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,input,query]
  | inr r => cases r <;> simp [store,input,query]

lemma check_tag (more : Bool) (rest m cat : List Bool) :
    Run program 2 (cfg .inspectTag (store rest m [] [] [more] cat [] [] []))
      (cfg (if more then .readLabel else .makeFresh) (store rest m [] [] [] cat [] [] [])) := by
  have hs : Step program (cfg .inspectTag (store rest m [] [] [more] cat [] [] []))
      (cfg (.checkTagEnd more) (store rest m [] [] [] cat [] [] [])) := by
    cases more <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
      funext k <;> cases k with
      | inl r => cases r <;> simp [store]
      | inr r => cases r <;> simp [store]
  have he : Step program (cfg (.checkTagEnd more) (store rest m [] [] [] cat [] [] []))
      (cfg (if more then .readLabel else .makeFresh) (store rest m [] [] [] cat [] [] [])) := by
    cases more <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag]
  exact .succ hs (.one he)

lemma header_call (more : Bool) (rest m cat : List Bool) :
    Run program 11 (cfg .readTag (store (tagBits [more]++false::rest) m [] [] [] cat [] [] []))
      (cfg (if more then .readLabel else .makeFresh) (store rest m [] [] [] cat [] [] [])) := by
  exact (read_tag_call [more] rest m cat).trans (check_tag more rest m cat)

lemma member_call (label rest m : List Bool) (seen : List (List Bool)) :
    Run program (NPStackCatalogueMember.memberCost label seen+2)
      (cfg .invokeMember (store rest m [] label [] (dataFields seen) [] [] []))
      (cfg .inspectMember (store rest m [] label [] (dataFields seen) [] []
        [decide (value label∈seen.map value)])) := by
  apply Macros.call_run Sum.inl State.member Sum.inl_injective member_extends
    (NPStackCatalogueMember.member_run label seen []) (.outer (.main .invokeMember)) (.outer (.main .inspectMember))
    (store rest m [] label [] (dataFields seen) [] [] [])
    (store rest m [] label [] (dataFields seen) [] [] [decide (value label∈seen.map value)])
  · rfl
  · rfl
  · intro k;cases k <;> rfl
  · intro k;cases k <;> rfl
  · intro k hk;cases k with
    | inl r => exact (hk r rfl).elim
    | inr r => cases r <;> rfl

lemma inspect_member (b : Bool) (label rest m cat : List Bool) :
    Step program (cfg .inspectMember (store rest m [] label [] cat [] [] [b]))
      (cfg (if b then .reject else .copyQuery) (store rest m [] label [] cat [] [] [])) := by
  cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,result] <;>
    funext k <;> cases k with
    | inl r => cases r <;> simp [store]
    | inr r => cases r <;> simp [store]

lemma copy_query_call (label rest m cat : List Bool) :
    Run program (5*label.length+4) (cfg .copyQuery (store rest m [] label [] cat [] [] []))
      (cfg .copyMaximum (store rest m [] label [] cat label [] [])) := by
  have h := outer_run (copy_call_store macroCode .readTag input fresh (q:=.copyQuery)
    rfl (by decide) (by decide) (by decide) (store rest m [] label [] cat [] [] []) rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,query,left]
  | inr r => cases r <;> simp [store,query,left]

lemma copy_maximum_call (label rest m cat : List Bool) :
    Run program (5*m.length+4) (cfg .copyMaximum (store rest m [] label [] cat label [] []))
      (cfg .compare (store rest m [] label [] cat label m [])) := by
  have h := outer_run (copy_call_store macroCode .readTag input fresh (q:=.copyMaximum)
    rfl (by decide) (by decide) (by decide) (store rest m [] label [] cat label [] []) rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,maximum,right]
  | inr r => cases r <;> simp [store,maximum,right]

lemma compare_call (label rest m cat : List Bool) :
    Run program (2*max label.length m.length+5)
      (cfg .compare (store rest m [] label [] cat label m []))
      (cfg .inspectOrder (store rest m [] label [] cat [] [] [leBits label m])) := by
  have h := Macros.call_run (R := Macros.compile macroCode .readTag input fresh)
    (normalizeMap left right result) (fun st => Label.local Main.compare (.compare st))
    (by intro a b h;cases a <;> cases b <;> simp_all [normalizeMap,left,right,result])
    (compare_extends macroCode .readTag input fresh (q:=.compare) rfl)
    (compare_leBits_run label m []) (.main .compare) (.main .inspectOrder)
    (store rest m [] label [] cat label m []) (store rest m [] label [] cat [] [] [leBits label m])
    (by rfl) (by rfl)
    (by intro k;cases k <;> rfl) (by intro k;cases k <;> rfl)
    (by
      intro k hk
      cases k with
      | inr r => cases r <;> rfl
      | inl r => cases r <;> simp [store] <;>
          first | exact (hk .left rfl).elim | exact (hk .right rfl).elim | exact (hk .result rfl).elim)
  convert outer_run h using 1 <;> omega

lemma inspect_order (b : Bool) (label rest m cat : List Bool) :
    Step program (cfg .inspectOrder (store rest m [] label [] cat [] [] [b]))
      (cfg (if b then .emitLabel else .clearMaximum) (store rest m [] label [] cat [] [] [])) := by
  cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,result] <;>
    funext k <;> cases k with
    | inl r => cases r <;> simp [store]
    | inr r => cases r <;> simp [store]

lemma replace_maximum_call (label rest m cat : List Bool) :
    Run program (m.length+1+(5*label.length+4))
      (cfg .clearMaximum (store rest m [] label [] cat [] [] []))
      (cfg .emitLabel (store rest label [] label [] cat [] [] [])) := by
  have hclear := outer_run (clear_loop macroCode .readTag input fresh .clearMaximum .replaceMaximum maximum rfl
    (store rest m [] label [] cat [] [] []))
  have he : Function.update (store rest m [] label [] cat [] [] []) maximum []=store rest [] [] label [] cat [] [] [] := by
    funext k;cases k with
    | inl r => cases r <;> simp [store,maximum]
    | inr r => cases r <;> simp [store,maximum]
  rw [he] at hclear
  have hcopy := outer_run (copy_call_store macroCode .readTag input fresh (q:=.replaceMaximum)
    rfl (by decide) (by decide) (by decide) (store rest [] [] label [] cat [] [] []) rfl)
  have he' : Function.update (store rest [] [] label [] cat [] [] []) maximum
      (label++[]) = store rest label [] label [] cat [] [] [] := by
    funext k;cases k with
    | inl r => cases r <;> simp [store,maximum]
    | inr r => cases r <;> simp [store,maximum]
  change Run program _ _ (cfg .emitLabel (Function.update (store rest [] [] label [] cat [] [] []) maximum (label++[]))) at hcopy
  rw [he'] at hcopy
  exact hclear.trans hcopy

lemma emit_label_call (label rest m cat : List Bool) :
    Run program (5*label.length+5) (cfg .emitLabel (store rest m [] label [] cat [] [] []))
      (cfg .readTag (store rest m [] [] [] (tagBits label++false::cat) [] [] [])) := by
  have h := outer_run (taggedEmit_call macroCode .readTag input fresh (q:=.emitLabel)
    rfl (by decide) (by decide) (by decide) (store rest m [] label [] cat [] [] []) rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,query,catalogue]
  | inr r => cases r <;> simp [store,query,catalogue]

lemma fresh_call (rest m cat : List Bool) :
    Run program (5*m.length+8) (cfg .makeFresh (store rest m [] [] [] cat [] [] []))
      (cfg .accept (store rest [] (addCarry m [] true).1 [] [] cat [] [] [])) := by
  have h := outer_run (add_call macroCode .readTag input fresh (q:=.makeFresh) rfl
    (by intro a b h;cases a <;> cases b <;> simp_all [addMap,maximum,right,scratch,fresh])
    (store rest m [] [] [] cat [] [] []) rfl rfl)
  convert h using 1
  · simp [store,maximum,right]
  · congr 1
    funext k;cases k with
    | inl r => cases r <;> simp [writes,store,maximum,right,fresh]
    | inr r => cases r <;> simp [writes,store,maximum,right,fresh]

end BalancedAssortments.NPCNF.StackCatalogue
