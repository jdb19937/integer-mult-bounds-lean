module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeInput

/-! Shared exchange-schedule bank: only the three coordinate inputs vary by
stage. Headers, arithmetic scratch and the host bank are reused by every call. -/

@[expose] public section
noncomputable section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

inductive BinaryScheduleReg (t₀ m : ℕ) where
  | bank (i : Fin (swapT t₀)) | coordinate (j : Fin m) (axis : Fin 3)
  | width | rowExp | gapExp | lowerExp | rows | block | canonical
  | header (i : Fin 5) | scratch (i : Fin 7)
  | triple | work | aux | ctmp | str | tmp
  deriving DecidableEq

def binaryScheduleStage {t₀ m : ℕ} (j : Fin m) : BinaryExchangeReg t₀ → BinaryScheduleReg t₀ m
  | .bank i => .bank i
  | .lower => .coordinate j 0
  | .upper => .coordinate j 1
  | .span => .coordinate j 2
  | .width => .width
  | .rowExp => .rowExp
  | .gapExp => .gapExp
  | .lowerExp => .lowerExp
  | .rows => .rows
  | .block => .block
  | .canonical => .canonical
  | .header i => .header i
  | .scratch i => .scratch i
  | .triple => .triple
  | .work => .work
  | .aux => .aux
  | .ctmp => .ctmp
  | .str => .str
  | .tmp => .tmp

theorem binaryScheduleStage_injective {t₀ m : ℕ} (j : Fin m) :
    Function.Injective (binaryScheduleStage (t₀ := t₀) j) := by
  intro r s h
  cases r <;> cases s <;> simp_all [binaryScheduleStage]

def binaryScheduleSlot {t₀ m : ℕ} : BinaryScheduleReg t₀ m → Fin (swapT t₀ + 25 + 3 * m)
  | .bank i => ⟨i.val, by have := i.isLt; omega⟩
  | .coordinate j axis => ⟨swapT t₀ + 25 + 3 * j.val + axis.val, by have := j.isLt; have := axis.isLt; omega⟩
  | .width => ⟨swapT t₀, by omega⟩
  | .rowExp => ⟨swapT t₀ + 1, by omega⟩
  | .gapExp => ⟨swapT t₀ + 2, by omega⟩
  | .lowerExp => ⟨swapT t₀ + 3, by omega⟩
  | .rows => ⟨swapT t₀ + 4, by omega⟩
  | .block => ⟨swapT t₀ + 5, by omega⟩
  | .canonical => ⟨swapT t₀ + 6, by omega⟩
  | .header i => ⟨swapT t₀ + 7 + i.val, by have := i.isLt; omega⟩
  | .scratch i => ⟨swapT t₀ + 12 + i.val, by have := i.isLt; omega⟩
  | .triple => ⟨swapT t₀ + 19, by omega⟩
  | .work => ⟨swapT t₀ + 20, by omega⟩
  | .aux => ⟨swapT t₀ + 21, by omega⟩
  | .ctmp => ⟨swapT t₀ + 22, by omega⟩
  | .str => ⟨swapT t₀ + 23, by omega⟩
  | .tmp => ⟨swapT t₀ + 24, by omega⟩

theorem binaryScheduleSlot_injective {t₀ m : ℕ} :
    Function.Injective (binaryScheduleSlot (t₀ := t₀) (m := m)) := by
  intro r s h
  have hv := congrArg Fin.val h
  cases r <;> cases s <;> simp only [binaryScheduleSlot] at hv
  all_goals first | rfl | (exfalso; omega) | (congr 1 <;> apply Fin.ext <;> omega)

def binaryScheduleInputWords {t₀ m n A : ℕ} (spec : Fin m → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) : BinaryScheduleReg t₀ m → List (Fin (A + 4))
  | .bank i => bankWords i
  | .coordinate j axis => binSyms Lc (![ (spec j).a, (spec j).b, (spec j).w ] axis)
  | .width => binSyms Lc n
  | .rows => rowBits.map bitSymbol
  | .block => binSyms L B
  | .str => stream
  | _ => []

theorem binaryScheduleInputWords_stage {t₀ m n A : ℕ} (spec : Fin m → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) (j : Fin m) (r : BinaryExchangeReg t₀) :
    binaryScheduleInputWords spec bankWords Lc L B rowBits stream (binaryScheduleStage j r) =
      binaryExchangeInputWords bankWords Lc L n (spec j).a (spec j).b (spec j).w B rowBits stream r := by
  cases r <;> rfl

def binaryScheduleInputBank {t₀ m n T A : ℕ} (slot : BinaryScheduleReg t₀ m → Fin T)
    (spec : Fin m → BlockExchangeSpec n) (bankWords : Fin (swapT t₀) → List (Fin (A + 4)))
    (Lc L B : ℕ) (rowBits : List Bool) (stream : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.extend slot (binaryScheduleInputWords spec bankWords Lc L B rowBits stream) (fun _ => [])

theorem binaryScheduleInputBank_at {t₀ m n T A : ℕ} (slot : BinaryScheduleReg t₀ m → Fin T)
    (hslot : Function.Injective slot) (spec : Fin m → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) (r : BinaryScheduleReg t₀ m) :
    binaryScheduleInputBank slot spec bankWords Lc L B rowBits stream (slot r) =
      binaryScheduleInputWords spec bankWords Lc L B rowBits stream r := hslot.extend_apply _ _ r

end IntegerMultBounds.MathlibTM2.Routing
