module

public import IntegerMultBounds.Machine.LayerControlBank
public import IntegerMultBounds.Machine.CompactGlobalRowHeaders
public import IntegerMultBounds.Machine.CompactChildHeadersArithmetic
public import IntegerMultBounds.Machine.CompactGlobalReservation

@[expose] public section
namespace IntegerMultBounds.Machine.LayerReservationHeaders
noncomputable section
variable {alphabet : ℕ}
open ActiveRepairRankHeadersCommands (State put)
open CompactGlobalRowHeaderOps (Op execute validSchedule scheduleCost)
open CompactGlobalRowPadding (rowAxes)
open CompactGadgetReservationCapacity (frontChunks backChunks)

abbrev command (operation : ActiveRepairRankHeadersCommands.Command) : Op := .ordinary (.command operation)
abbrev product (ports : Fin 3 → Fin 28) (injective : Function.Injective ports) : Op := .ordinary (.product ports injective)

def guard (precision : ℕ) := 4*Nat.clog 2 precision+6
def nativeWidth (activeCount chunkWidth wordWidth : ℕ) := wordWidth+4*(activeCount*chunkWidth)+4
def capacity (precision axes : ℕ) := axes*guard precision
def frontBits (precision axes chunkWidth : ℕ) := RoundedRowDescriptor.rounded (2*capacity precision axes) chunkWidth
def backBits (precision axes chunkWidth : ℕ) := RoundedRowDescriptor.rounded (capacity precision axes) chunkWidth
def reservationAxes (roleCount arity precision axes chunkWidth : ℕ) :=
  rowAxes roleCount arity axes+frontChunks axes (guard precision) chunkWidth+backChunks axes (guard precision) chunkWidth

def guardSchedule : List Op := [
  .logarithm 2 ![0,10] (by decide),command (.copy 10 11 (by decide)),
  command (.add 11 10 (by decide)),command (.add 11 10 (by decide)),command (.add 11 10 (by decide)),
  .constant 6 27,command (.add 11 27 (by decide)),command (.erase 27)]

def widthSchedule : List Op := [
  product ![6,3,12] (by decide),command (.copy 8 13 (by decide)),
  command (.add 13 12 (by decide)),command (.add 13 12 (by decide)),
  command (.add 13 12 (by decide)),command (.add 13 12 (by decide)),
  .constant 4 27,command (.add 13 27 (by decide)),command (.erase 27)]

def fieldSchedule : List Op := [
  product ![1,11,14] (by decide),command (.copy 14 27 (by decide)),command (.add 27 14 (by decide)),
  .ordinary (.round ![27,6,15] (by decide)),.ordinary (.round ![14,6,16] (by decide)),command (.erase 27)]

def rowSchedule (roleCount arity : ℕ) : List Op := [
  .constant (Nat.clog 2 roleCount) 24,command (.copy 1 25 (by decide)),command (.add 25 1 (by decide)),
  .logarithm arity ![25,26] (by decide),product ![24,26,17] (by decide),
  command (.erase 24),command (.erase 25),command (.erase 26)]

def original (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  LayerControlBank.initial precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth

def guarded (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  put (put (original precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    10 (Nat.clog 2 precision)) 11 (guard precision)

def widened (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  put (put (guarded precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    12 (activeCount*chunkWidth)) 13 (nativeWidth activeCount chunkWidth wordWidth)

def reserved (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  put (put (put (widened precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    14 (capacity precision axes)) 15 (frontBits precision axes chunkWidth)) 16 (backBits precision axes chunkWidth)

def rowReady (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  put (reserved precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    17 (rowAxes roleCount arity axes)

def countSchedule : List CompactChildHeadersArithmetic.Op := [
  .quotient ![15,6,18] (by decide),.quotient ![16,6,19] (by decide),
  .existing (.command (.copy 17 20 (by decide))),.existing (.command (.add 20 18 (by decide))),
  .existing (.command (.add 20 19 (by decide))),.existing (.command (.copy 20 21 (by decide))),
  .existing (.command (.add 21 20 (by decide)))]

def finished (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  put (put (put (put (rowReady roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    18 (frontChunks axes (guard precision) chunkWidth)) 19 (backChunks axes (guard precision) chunkWidth))
    20 (reservationAxes roleCount arity precision axes chunkWidth)) 21 (2*reservationAxes roleCount arity precision axes chunkWidth)

theorem guard_executes (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :
    execute guardSchedule (original precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)=
      guarded precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth := by
  funext slot
  fin_cases slot <;> simp [guardSchedule,execute,CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,original,guarded,guard,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,put,Function.update]
  omega

theorem guard_valid (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 0<precision) :
    validSchedule guardSchedule (original precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  simp [guardSchedule,validSchedule,CompactGlobalRowHeaderOps.valid,CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,original,LayerControlBank.initial,LayerControlBank.values,LayerHeaderRead.fields,
    put,Function.update,precisionPositive]

theorem width_executes (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :
    execute widthSchedule (guarded precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)=
      widened precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth := by
  funext slot
  fin_cases slot <;> simp [widthSchedule,execute,CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,guarded,widened,original,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,nativeWidth,put,Function.update]
  all_goals ring

theorem width_valid (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (chunkPositive : 0<chunkWidth) :
    validSchedule widthSchedule (guarded precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  simp [widthSchedule,validSchedule,CompactGlobalRowHeaderOps.valid,CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,guarded,original,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,put,Function.update,chunkPositive]

theorem field_executes (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :
    execute fieldSchedule (widened precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)=
      reserved precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth := by
  funext slot
  fin_cases slot <;> simp [fieldSchedule,execute,CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,reserved,widened,guarded,original,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,capacity,frontBits,backBits,put,Function.update,Nat.mul_comm,←two_mul]

theorem field_valid (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (axesPositive : 0<axes) (chunkPositive : 0<chunkWidth) :
    validSchedule fieldSchedule (widened precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  have guardPositive : 0<guard precision := by unfold guard; omega
  have capacityPositive : 0<axes*guard precision := Nat.mul_pos axesPositive guardPositive
  simp [fieldSchedule,validSchedule,CompactGlobalRowHeaderOps.valid,CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,widened,guarded,original,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,put,Function.update,axesPositive,chunkPositive]
  omega

theorem row_executes (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :
    execute (rowSchedule roleCount arity) (reserved precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)=
      rowReady roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth := by
  funext slot
  fin_cases slot <;> simp [rowSchedule,execute,CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,rowReady,reserved,widened,guarded,original,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,rowAxes,put,Function.update,two_mul,Nat.mul_comm]

theorem row_valid (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (rolesPositive : 2≤roleCount) (arityPositive : 2≤arity) (axesPositive : 0<axes) :
    validSchedule (rowSchedule roleCount arity) (reserved precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  have logarithmPositive := CompactGlobalRowHeaders.logc_positive roleCount rolesPositive
  simp [rowSchedule,validSchedule,CompactGlobalRowHeaderOps.valid,CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,reserved,widened,guarded,original,LayerControlBank.initial,LayerControlBank.values,
    LayerHeaderRead.fields,put,Function.update,arityPositive,axesPositive,logarithmPositive]

theorem front_bits (precision axes chunkWidth : ℕ) (axesPositive : 0<axes) (chunkPositive : 0<chunkWidth) :
    frontBits precision axes chunkWidth=frontChunks axes (guard precision) chunkWidth*chunkWidth := by
  rw [frontBits,RoundedRowDescriptor.rounded_eq_ceiling _ _ (by unfold capacity guard; positivity) chunkPositive]
  exact Nat.mul_comm _ _

theorem back_bits (precision axes chunkWidth : ℕ) (axesPositive : 0<axes) (chunkPositive : 0<chunkWidth) :
    backBits precision axes chunkWidth=backChunks axes (guard precision) chunkWidth*chunkWidth := by
  rw [backBits,RoundedRowDescriptor.rounded_eq_ceiling _ _ (by unfold capacity guard; positivity) chunkPositive]
  exact Nat.mul_comm _ _

theorem count_executes (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (axesPositive : 0<axes) (chunkPositive : 0<chunkWidth) :
    CompactChildHeadersArithmetic.execute countSchedule
      (rowReady roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)=
      finished roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth := by
  have frontQuotient : frontBits precision axes chunkWidth/chunkWidth=frontChunks axes (guard precision) chunkWidth := by
    rw [front_bits _ _ _ axesPositive chunkPositive,Nat.mul_div_cancel _ chunkPositive]
  have backQuotient : backBits precision axes chunkWidth/chunkWidth=backChunks axes (guard precision) chunkWidth := by
    rw [back_bits _ _ _ axesPositive chunkPositive,Nat.mul_div_cancel _ chunkPositive]
  funext slot
  fin_cases slot <;> simp [countSchedule,CompactChildHeadersArithmetic.execute,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,finished,rowReady,reserved,widened,guarded,
    original,LayerControlBank.initial,LayerControlBank.values,LayerHeaderRead.fields,put,Function.update,frontQuotient,backQuotient,
    reservationAxes]
  omega

theorem count_valid (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (chunkPositive : 0<chunkWidth) :
    CompactChildHeadersArithmetic.validSchedule countSchedule
      (rowReady roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  simp [countSchedule,CompactChildHeadersArithmetic.validSchedule,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,rowReady,reserved,widened,guarded,
    original,LayerControlBank.initial,LayerControlBank.values,LayerHeaderRead.fields,put,Function.update,chunkPositive]

def prefixSchedule (roleCount arity : ℕ) := guardSchedule++widthSchedule++fieldSchedule++rowSchedule roleCount arity
def program (roleCount arity : ℕ) := seq (CompactGlobalRowHeaderOps.compile (a:=alphabet) (prefixSchedule roleCount arity)).2
  (CompactChildHeadersArithmetic.compile (a:=alphabet) countSchedule).2
def cost (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  scheduleCost (prefixSchedule roleCount arity) (original precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)+1+
    CompactChildHeadersArithmetic.scheduleCost countSchedule
      (rowReady roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)

private theorem valid_append (head tail : List Op) (state : State) :
    validSchedule (head++tail) state ↔ validSchedule head state ∧ validSchedule tail (execute head state) := by
  induction head generalizing state with
  | nil => simp [validSchedule,execute]
  | cons operation head inductionHypothesis => simp only [List.cons_append,validSchedule,execute,inductionHypothesis,and_assoc]

theorem runs (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (rolesPositive : 2≤roleCount) (arityPositive : 2≤arity) (precisionPositive : 0<precision)
    (axesPositive : 0<axes) (chunkPositive : 0<chunkWidth) :
    HoareTime (program (alphabet:=alphabet) roleCount arity)
      (· = ActiveRepairRankHeadersCommands.bank (original precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth))
      (· = ActiveRepairRankHeadersCommands.bank
        (finished roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth))
      (cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  have prefixValid : validSchedule (prefixSchedule roleCount arity)
      (original precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
    simp only [prefixSchedule,List.append_assoc,valid_append,guard_executes,width_executes,field_executes]
    exact ⟨guard_valid _ _ _ _ _ _ _ _ _ precisionPositive,width_valid _ _ _ _ _ _ _ _ _ chunkPositive,
      field_valid _ _ _ _ _ _ _ _ _ axesPositive chunkPositive,row_valid _ _ _ _ _ _ _ _ _ _ _ rolesPositive arityPositive axesPositive⟩
  have prefixRun := CompactGlobalRowHeaderOps.schedule_runs (a:=alphabet) (prefixSchedule roleCount arity) _ prefixValid
  simp only [prefixSchedule,CompactGlobalRowHeaderOps.execute_append,guard_executes,width_executes,field_executes,row_executes] at prefixRun
  have countRun := CompactChildHeadersArithmetic.schedule_runs (a:=alphabet) countSchedule
    (rowReady roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    (count_valid roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth chunkPositive)
  rw [count_executes _ _ _ _ _ _ _ _ _ _ _ axesPositive chunkPositive] at countRun
  exact prefixRun.seq countRun

end
end IntegerMultBounds.Machine.LayerReservationHeaders
