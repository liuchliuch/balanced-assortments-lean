import BalancedAssortments.NPStackMacroRuns

/-! Concrete store-update rules for expanded macro calls. Every entry/return
jump and every primitive bit step is counted; arbitrary untouched registers are
preserved by the proved frame condition. -/
namespace BalancedAssortments.NPStack.Macros
open NPStack NPStackFields
variable {K Q : Type*} [DecidableEq K]
variable (m : Q → Macro K Q) (start : Q) (input output : K)

lemma copy_call_store {q next : Q} {source scratch target : K}
    (hm : m q=.copy source scratch target next)
    (hsw : source≠scratch) (hst : source≠target) (hwt : scratch≠target)
    (s : K → List Bool) (hw : s scratch=[]) :
    Run (compile m start input output) (5*(s source).length+4)
      ⟨.main q,s⟩ ⟨.main next,Function.update s target (s source++s target)⟩ := by
  have hinj : Function.Injective (copyMap source scratch target) := by
    intro a b h;cases a <;> cases b <;> simp_all [copyMap]
  have hr := call_run (copyMap source scratch target) (fun st=>Label.local q (.copy st)) hinj
    (copy_extends m start input output hm) (copy_run (s source) (s target))
    (.main q) (.main next) s (Function.update s target (s source++s target))
    (by simp [compile,code,returnCode,copyProgram,NPStackFieldData.readProgram,NPStackFieldData.emitProgram,hm,copyConfig,NPStackFieldData.readConfig,NPStackFieldData.emitConfig]) (by simp [compile,code,returnCode,copyProgram,NPStackFieldData.readProgram,NPStackFieldData.emitProgram,hm,copyConfig,NPStackFieldData.readConfig,NPStackFieldData.emitConfig])
    (by intro k;cases k <;> simp [copyMap,copyConfig,copyStacks,hw])
    (by intro k;cases k <;> simp [copyMap,copyConfig,copyStacks,hw,Function.update_apply,hst,hwt])
    (by intro k hk;exact Function.update_of_ne (Ne.symm (hk .target)) _ _)
  convert hr using 1 <;> omega

lemma taggedEmit_call {q next : Q} {source scratch target : K}
    (hm : m q=.taggedEmit source scratch target next)
    (hsw : source≠scratch) (hst : source≠target) (hwt : scratch≠target)
    (s : K → List Bool) (hw : s scratch=[]) :
    Run (compile m start input output) (5*(s source).length+5)
      ⟨.main q,s⟩ ⟨.main next,Function.update (Function.update s source []) target
        (tagBits (s source)++false::s target)⟩ := by
  have hinj : Function.Injective (dataMap source scratch target) := by
    intro a b h;cases a <;> cases b <;> simp_all [dataMap]
  have hr := call_run (dataMap source scratch target) (fun st=>Label.local q (.taggedEmit st)) hinj
    (taggedEmit_extends m start input output hm) (NPStackFieldData.emit_field (s source) (s target))
    (.main q) (.main next) s
    (Function.update (Function.update s source []) target (tagBits (s source)++false::s target))
    (by simp [compile,code,returnCode,copyProgram,NPStackFieldData.readProgram,NPStackFieldData.emitProgram,hm,copyConfig,NPStackFieldData.readConfig,NPStackFieldData.emitConfig]) (by simp [compile,code,returnCode,copyProgram,NPStackFieldData.readProgram,NPStackFieldData.emitProgram,hm,copyConfig,NPStackFieldData.readConfig,NPStackFieldData.emitConfig])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.emitConfig,NPStackFieldData.dataStacks,hw])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.emitConfig,NPStackFieldData.dataStacks,
      hw,Function.update_apply,hst,hwt,Ne.symm hsw])
    (by
      intro k hk
      have ht : k≠target := Ne.symm (hk .output)
      have hi : k≠source := Ne.symm (hk .input)
      simp [Function.update_apply,ht,hi])
  convert hr using 1 <;> omega

lemma taggedRead_call {q yes no : Q} {source scratch target : K}
    (hm : m q=.taggedRead source scratch target yes no)
    (hsw : source≠scratch) (hst : source≠target) (hwt : scratch≠target)
    (s : K → List Bool) (bits rest : List Bool) (hi : s source=tagBits bits++false::rest)
    (hw : s scratch=[]) :
    Run (compile m start input output) (5*bits.length+4)
      ⟨.main q,s⟩ ⟨.main yes,Function.update (Function.update s source rest) target (bits++s target)⟩ := by
  have hinj : Function.Injective (dataMap source scratch target) := by
    intro a b h;cases a <;> cases b <;> simp_all [dataMap]
  have hr := call_run (dataMap source scratch target) (fun st=>Label.local q (.taggedRead st)) hinj
    (taggedRead_extends m start input output hm) (NPStackFieldData.read_field bits rest (s target))
    (.main q) (.main yes) s (Function.update (Function.update s source rest) target (bits++s target))
    (by simp [compile,code,returnCode,copyProgram,NPStackFieldData.readProgram,NPStackFieldData.emitProgram,hm,copyConfig,NPStackFieldData.readConfig,NPStackFieldData.emitConfig]) (by simp [compile,code,returnCode,copyProgram,NPStackFieldData.readProgram,NPStackFieldData.emitProgram,hm,copyConfig,NPStackFieldData.readConfig,NPStackFieldData.emitConfig])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.readConfig,NPStackFieldData.dataStacks,hw,hi])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.readConfig,NPStackFieldData.dataStacks,
      hw,Function.update_apply,hst,hwt,Ne.symm hsw])
    (by
      intro k hk
      have ht : k≠target := Ne.symm (hk .output)
      have hi : k≠source := Ne.symm (hk .input)
      simp [Function.update_apply,ht,hi])
  convert hr using 1 <;> omega

end BalancedAssortments.NPStack.Macros
