import BalancedAssortments.NPStackMacroRuns
import BalancedAssortments.ComplexitySourceEncoding

/-! Finite operational positive Subset Sum to BMS transducer. It retains every
positive input item (oversized items are harmless by model_correct), streams
signed product records in reverse item order, and rejects no input by fiat:
all malformed/illegal instances produce the fixed legal source no-instance. -/
namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexitySourceModel

inductive Reg
  | wireIn | wireOut | target | item | triple | quintuple | count | price | temp1 | temp2 | temp3
  deriving DecidableEq, Fintype

inductive Stage
  | readTarget | normalizeTarget | positiveTarget | restoreTarget (b : Bool)
  | tripleLeft | tripleRight | tripleShift | tripleAdd | tripleNormalize
  | quintupleLeft | quintupleRight | quintupleShiftOne | quintupleShiftTwo | quintupleAdd | quintupleNormalize
  | initializeCount | probe (seen : Bool) | restoreInput (seen bit : Bool)
  | readItem | normalizeItem | positiveItem | restoreItem (b : Bool)
  | countOne | countAdd | countNormalize
  | priceLeft | priceRight | priceAdd | priceNormalize
  | emitItemDen | emitItemNegative | attractionCopy | emitAttraction
  | priceDenOne | emitPriceDen | emitPriceNegative | emitPrice
  | header (i : Fin 14) | headerTwo (i : Fin 14) | headerEncode (i : Fin 14)
  | badClear | badEmit (i : Fin (fixedNoSource.length+1)) | done
  deriving DecidableEq, Fintype

inductive HeaderValue | zero | one | two | triple | quintuple | count
  deriving DecidableEq

def headerValue (i : Fin 14) : HeaderValue :=
  match i.val with
  | 1 | 4 | 7 | 10 => .zero
  | 5 => .quintuple
  | 8 => .triple
  | 12 => .two
  | 13 => .count
  | _ => .one

def afterHeader (i : Fin 14) : Stage := if h : i.val+1<14 then .header ⟨i.val+1,h⟩ else .done

def table : Stage → Macro Reg Stage
  | .readTarget => .read .wireIn .temp3 .temp2 .temp1 .normalizeTarget .badClear
  | .normalizeTarget => .normalize .temp1 .temp2 .target .positiveTarget
  | .positiveTarget => .pop .target .badClear (.restoreTarget false) (.restoreTarget true)
  | .restoreTarget b => .push .target b .tripleLeft
  | .tripleLeft => .copy .target .temp3 .temp1 .tripleRight
  | .tripleRight => .copy .target .temp3 .temp2 .tripleShift
  | .tripleShift => .push .temp2 false .tripleAdd
  | .tripleAdd => .add .temp1 .temp2 .temp3 .price false .tripleNormalize
  | .tripleNormalize => .normalize .price .temp3 .triple .quintupleLeft
  | .quintupleLeft => .copy .target .temp3 .temp1 .quintupleRight
  | .quintupleRight => .copy .target .temp3 .temp2 .quintupleShiftOne
  | .quintupleShiftOne => .push .temp2 false .quintupleShiftTwo
  | .quintupleShiftTwo => .push .temp2 false .quintupleAdd
  | .quintupleAdd => .add .temp1 .temp2 .temp3 .price false .quintupleNormalize
  | .quintupleNormalize => .normalize .price .temp3 .quintuple .initializeCount
  | .initializeCount => .push .count true (.probe false)
  | .probe seen => .pop .wireIn (if seen then .header 0 else .badClear)
      (.restoreInput seen false) (.restoreInput seen true)
  | .restoreInput _ b => .push .wireIn b .readItem
  | .readItem => .read .wireIn .temp3 .temp2 .temp1 .normalizeItem .badClear
  | .normalizeItem => .normalize .temp1 .temp2 .item .positiveItem
  | .positiveItem => .pop .item .badClear (.restoreItem false) (.restoreItem true)
  | .restoreItem b => .push .item b .countOne
  | .countOne => .push .temp1 true .countAdd
  | .countAdd => .add .count .temp1 .temp2 .temp3 false .countNormalize
  | .countNormalize => .normalize .temp3 .temp2 .count .priceLeft
  | .priceLeft => .copy .triple .temp3 .temp1 .priceRight
  | .priceRight => .copy .item .temp3 .temp2 .priceAdd
  | .priceAdd => .add .temp1 .temp2 .price .temp3 false .priceNormalize
  | .priceNormalize => .normalize .temp3 .temp2 .price .emitItemDen
  | .emitItemDen => .encode .item .temp2 .temp3 .wireOut .emitItemNegative
  | .emitItemNegative => .encode .temp1 .temp2 .temp3 .wireOut .attractionCopy
  | .attractionCopy => .copy .target .temp2 .temp1 .emitAttraction
  | .emitAttraction => .encode .temp1 .temp2 .temp3 .wireOut .priceDenOne
  | .priceDenOne => .push .temp1 true .emitPriceDen
  | .emitPriceDen => .encode .temp1 .temp2 .temp3 .wireOut .emitPriceNegative
  | .emitPriceNegative => .encode .temp1 .temp2 .temp3 .wireOut .emitPrice
  | .emitPrice => .encode .price .temp2 .temp3 .wireOut (.probe true)
  | .header i => match headerValue i with
    | .zero => .jump (.headerEncode i)
    | .one => .push .temp1 true (.headerEncode i)
    | .two => .push .temp1 true (.headerTwo i)
    | .triple => .copy .triple .temp2 .temp1 (.headerEncode i)
    | .quintuple => .copy .quintuple .temp2 .temp1 (.headerEncode i)
    | .count => .copy .count .temp2 .temp1 (.headerEncode i)
  | .headerTwo i => .push .temp1 false (.headerEncode i)
  | .headerEncode i => .encode .temp1 .temp2 .temp3 .wireOut (afterHeader i)
  | .badClear => .pop .wireOut (.badEmit 0) .badClear .badClear
  | .badEmit i => if h : i.val<fixedNoSource.length then
      .push .wireOut (fixedNoSource.reverse.get ⟨i.val,by simpa using h⟩) (.badEmit ⟨i.val+1,by omega⟩)
    else .halt true
  | .done => .halt true

def program : Program Reg (Label Stage) := compile table .readTarget .wireIn .wireOut

def finiteProgram : FiniteProgram where
  K := Reg
  Q := Label Stage
  program := program

lemma program_noChoice : NoChoice program := compile_noChoice table .readTarget .wireIn .wireOut

end BalancedAssortments.NPStackSourceReduction
