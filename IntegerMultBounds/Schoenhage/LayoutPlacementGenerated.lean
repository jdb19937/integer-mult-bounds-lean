module

public import IntegerMultBounds.Schoenhage.CertifiedBinOf

/-! Generated finite placements. Do not edit; regenerate from the manifest. -/
@[expose] public section
namespace IntegerMultBounds.Schoenhage.LayoutPlacementGenerated
open IntegerMultBounds.Machine IntegerMultBounds.Schoenhage
open IntegerMultBounds.Schoenhage.CertifiedSequence
open IntegerMultBounds.Schoenhage.LayoutGenSetup
open IntegerMultBounds.Resampling.Script
noncomputable section

def widthConverterSlots : Fin 5 → Fin 48 := ![34, 44, 45, 46, 10]
theorem widthConverter_injective : Function.Injective widthConverterSlots := by decide
def widthConverterProgram : Cmd 0 48 := binOf.map widthConverterSlots widthConverter_injective

def widthConverterCertificate (value : ℕ) (bank : Fin 48 → WTape) (ready : bank ∘ widthConverterSlots = bbank value emp emp) :=
  ofRuns (placed_update widthConverterSlots widthConverter_injective bank ready 1
    (reg (bin value)) (runs_binOf_update value))

def widthConverterCost (value : ℕ) : ℕ := (ofRuns (runs_binOf_update value)).bound

theorem widthConverter_runs (value : ℕ) (bank : Fin 48 → WTape) (ready : bank ∘ widthConverterSlots = bbank value emp emp) :
    Runs widthConverterProgram bank (· = Function.update bank 44 (reg (bin value))) (widthConverterCost value) :=
  (widthConverterCertificate value bank ready).runs

theorem widthConverter_hoare (value : ℕ) (bank : Fin 48 → WTape) (ready : bank ∘ widthConverterSlots = bbank value emp emp) :
    HoareTime (compile (by decide) widthConverterProgram).2
      (· = enc bank) (· = enc (Function.update bank 44 (reg (bin value)))) (widthConverterCost value) :=
  (widthConverterCertificate value bank ready).hoare (by decide)

def chunkConverterSlots : Fin 5 → Fin 48 := ![33, 24, 45, 46, 10]
theorem chunkConverter_injective : Function.Injective chunkConverterSlots := by decide
def chunkConverterProgram : Cmd 0 48 := binOf.map chunkConverterSlots chunkConverter_injective

def chunkConverterCertificate (value : ℕ) (bank : Fin 48 → WTape) (ready : bank ∘ chunkConverterSlots = bbank value emp emp) :=
  ofRuns (placed_update chunkConverterSlots chunkConverter_injective bank ready 1
    (reg (bin value)) (runs_binOf_update value))

def chunkConverterCost (value : ℕ) : ℕ := (ofRuns (runs_binOf_update value)).bound

theorem chunkConverter_runs (value : ℕ) (bank : Fin 48 → WTape) (ready : bank ∘ chunkConverterSlots = bbank value emp emp) :
    Runs chunkConverterProgram bank (· = Function.update bank 24 (reg (bin value))) (chunkConverterCost value) :=
  (chunkConverterCertificate value bank ready).runs

theorem chunkConverter_hoare (value : ℕ) (bank : Fin 48 → WTape) (ready : bank ∘ chunkConverterSlots = bbank value emp emp) :
    HoareTime (compile (by decide) chunkConverterProgram).2
      (· = enc bank) (· = enc (Function.update bank 24 (reg (bin value)))) (chunkConverterCost value) :=
  (chunkConverterCertificate value bank ready).hoare (by decide)

end
end IntegerMultBounds.Schoenhage.LayoutPlacementGenerated
