import BalancedAssortments.NPCNFStackAllocation
import BalancedAssortments.NPCNFStackCatalogueOutputCost
import BalancedAssortments.NPStackFieldsEncode

/-! Actual finite linkage of formula transformation, catalogue assembly and
flat bit serialization. The input here is the checked/prepared record state;
the preceding raw parser/catalogue validator is a separate program. -/
namespace BalancedAssortments.NPCNF.StackTransform
open NPStack NPStack.Macros NPStackFields Encoding
abbrev Register := Sum StackChain.Register Unit
inductive State
  | formula (q : StackFormula.State)
  | catalogue (q : Label StackCatalogueOutput.State)
  | encode (q : NPStackFieldsEncode.State)
  deriving DecidableEq,Fintype

def catalogueMap : StackCatalogueOutput.Register → Register
  | .original => .inr () | .allocated => .inl .allocated | .output => .inl .output
  | .scratchRead => .inl .scratchRead | .scratchEmit => .inl .scratchCopy | .label => .inl .temporary

def encodeMap : NPStackFieldsEncode.Stack → Register
  | .input => .inl .output | .accumulator => .inl .savedOutput | .payload => .inl .temporary
  | .scratch => .inl .scratchRead | .count => .inl .one | .output => .inl .input

def code : State → Instr Register State
  | .formula (.outer (.main .accept)) => .jump (.catalogue (.main .marker0))
  | .formula q => (StackFormula.program.code q).rename Sum.inl State.formula
  | .catalogue (.main .accept) => .jump (.encode (.probe false))
  | .catalogue q => (StackCatalogueOutput.program.code q).rename catalogueMap State.catalogue
  | .encode q => (NPStackFieldsEncode.program.code q).rename encodeMap State.encode

def program : Program Register State :=
  ⟨code,.formula (.outer (.main .readHeader)),.inl .input,.inl .input⟩

def store (input fresh output allocated original : List Bool) : Register → List Bool
  | .inl k => StackChain.store input [] [] fresh output allocated k
  | .inr _ => original

def result (next : List Bool) (input : Raw) : Raw :=
  ⟨input.catalog.reverse++StackFormula.formulaLabels next input.formula,(bitFormula next input.formula).1.1⟩

lemma formula_extends : CodeExtends StackFormula.program program Sum.inl State.formula := by
  intro q h
  cases q with
  | outer q => cases q with
    | main q => cases q <;> first | exact False.elim (h true rfl) | rfl
    | «local» q st => rfl
  | chain q => rfl
lemma catalogue_extends : CodeExtends StackCatalogueOutput.program program catalogueMap State.catalogue := by
  intro q h
  cases q with
  | main q => cases q <;> first | exact False.elim (h true rfl) | rfl
  | «local» q st => rfl
lemma encode_extends : CodeExtends NPStackFieldsEncode.program program encodeMap State.encode := by intro q h;rfl

lemma catalogue_injective : Function.Injective catalogueMap := by intro a b h;cases a <;> cases b <;> simp_all [catalogueMap]
lemma encode_injective : Function.Injective encodeMap := by intro a b h;cases a <;> cases b <;> simp_all [encodeMap]

def cost (next : List Bool) (input : Raw) : ℕ :=
  StackFormula.formulaCost next input.formula []+
  (StackCatalogueOutput.recordsCost input.catalog+StackCatalogueOutput.recordsCost (StackFormula.formulaLabels next input.formula).reverse+3)+
  (22*NPStackFieldsEncode.volume (fields (result next input))+19*(fields (result next input)).length+2)+2

/-- Complete bit-for-bit output refinement for the linked finite transformation
of checked CNF records. Fresh labels and the original label order are explicit. -/
theorem transform_run (next : List Bool) (input : Raw) :
    Run program (cost next input)
      ⟨.formula (.outer (.main .readHeader)),store (StackFormula.formulaData input.formula) next [] [] (dataFields input.catalog)⟩
      ⟨.encode .accept,store (encode (result next input)) (bitFormula next input.formula).1.2 [] [] []⟩ := by
  let next' := (bitFormula next input.formula).1.2
  let formula := StackFormula.formulaData (bitFormula next input.formula).1.1
  let allocated := StackFormula.formulaAllocated next input.formula
  have hf := StackFormula.formula_run next input.formula [] []
  simp only [List.nil_append,List.append_nil] at hf
  have h1 := hf.relocate_exact Sum.inl State.formula Sum.inl_injective formula_extends
    (c' := ⟨.formula (.outer (.main .readHeader)),store (StackFormula.formulaData input.formula) next [] [] (dataFields input.catalog)⟩)
    (d' := ⟨.formula (.outer (.main .accept)),store [] next' formula allocated (dataFields input.catalog)⟩)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr u => rfl)
  have h12 : Step program ⟨.formula (.outer (.main .accept)),store [] next' formula allocated (dataFields input.catalog)⟩
      ⟨.catalogue (.main .marker0),store [] next' formula allocated (dataFields input.catalog)⟩ := by
    simp [Step,successors,program,code]
  have hc := StackCatalogueOutput.catalogue_run input.catalog (StackFormula.formulaLabels next input.formula).reverse formula
  simp only [List.reverse_reverse] at hc
  have hout : dataFields (catalogFields (input.catalog.reverse++StackFormula.formulaLabels next input.formula))++formula=
      dataFields (fields (result next input)) := by
    simp [fields,result,formula,StackFormula.formulaData,dataFields,List.flatMap_append]
  rw [hout] at hc
  have h2 := hc.relocate_exact catalogueMap State.catalogue catalogue_injective catalogue_extends
    (c' := ⟨.catalogue (.main .marker0),store [] next' formula allocated (dataFields input.catalog)⟩)
    (d' := ⟨.catalogue (.main .accept),store [] next' (dataFields (fields (result next input))) [] []⟩)
    ⟨rfl,by intro k;cases k <;> simp [catalogueMap,store,StackChain.store,StackCatalogueOutput.cfg,StackCatalogueOutput.store,
      allocated,StackFormula.formulaAllocated_fields]⟩
    ⟨rfl,by intro k;cases k <;> rfl⟩
    (by
      intro k hk
      have h1:=hk .original;have h2:=hk .allocated;have h3:=hk .output
      cases k with
      | inl k => cases k <;> simp_all [store,StackChain.store,catalogueMap]
      | inr u => cases u;simp_all [catalogueMap])
  have h23 : Step program ⟨.catalogue (.main .accept),store [] next' (dataFields (fields (result next input))) [] []⟩
      ⟨.encode (.probe false),store [] next' (dataFields (fields (result next input))) [] []⟩ := by
    simp [Step,successors,program,code]
  have he := NPStackFieldsEncode.encode_fields (fields (result next input)) []
  simp only [List.append_nil] at he
  have h3 := he.relocate_exact encodeMap State.encode encode_injective encode_extends
    (c' := ⟨.encode (.probe false),store [] next' (dataFields (fields (result next input))) [] []⟩)
    (d' := ⟨.encode .accept,store (encode (result next input)) next' [] [] []⟩)
    ⟨rfl,by intro k;cases k <;> rfl⟩ ⟨rfl,by intro k;cases k <;> rfl⟩
    (by
      intro k hk
      have h1:=hk .input;have h2:=hk .output
      cases k with
      | inl k => cases k <;> simp_all [store,StackChain.store,encodeMap]
      | inr u => rfl)
  have hh := h1.trans (Run.succ h12 (h2.trans (Run.succ h23 h3)))
  convert hh using 1 <;> dsimp only [cost] <;> omega

end BalancedAssortments.NPCNF.StackTransform
