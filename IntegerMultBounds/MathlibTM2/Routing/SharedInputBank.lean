module

public import IntegerMultBounds.MathlibTM2.Routing.SourceMask
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScale
public import IntegerMultBounds.MathlibTM2.Routing.UnaryPredecessor
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySharedSetup

/-!
# Generating shared raw inputs from binary dimensions

The block-width binary input is reused directly. The other three raw shared
words are generated from the binary address width and row count. Five scratch
tapes are reused and restored; no unary address width or first mask is supplied.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive SharedInputReg where
  | width | rows | block | records | field | mask | scratch (i : Fin 5)
  deriving DecidableEq

def sharedInputConfig {T : ℕ} (rg : SharedInputReg → Fin T) : Fin 4 → Fin T :=
  ![rg .block, rg .records, rg .field, rg .mask]

def sharedInputBank {T A : ℕ} (R : Fin T → List (Fin (A + 4))) (rg : SharedInputReg → Fin T)
    (n rows : ℕ) (rowLength : ℕ) :=
  Function.update (Function.update (Function.update R (rg .field) (List.replicate n tick))
    (rg .records) (binSyms (n + rowLength) (rows * 2 ^ n))) (rg .mask) (binSyms n 1)

def sharedInputProgram {T Q A : ℕ} {P U : Type} (rg : SharedInputReg → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg .width) (rg .field) (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2)))
    (.seq (binaryScaleProgram (rg .field) (rg .rows) (rg .records) (rg (.scratch 1)) (rg (.scratch 2)))
      (.seq (unaryPredecessorProgram (rg .field) (rg (.scratch 3)) (rg (.scratch 1)) (rg (.scratch 2)))
        (.seq (sourceMaskProgram (rg (.scratch 4)) (rg (.scratch 3)) (rg .mask) (rg (.scratch 1)) (rg (.scratch 2)))
          (bclear (rg (.scratch 3))))))

/-- Shifted counter bits are exactly the padded binary record-count operand. -/
theorem binaryScale_binSyms {A : ℕ} (e : ℕ) (bs : List Bool) :
    List.replicate e (bitSymbol (a := A) false) ++ bs.map bitSymbol =
      binSyms (e + bs.length) (2 ^ e * Counter.value bs) := by
  have h := binaryBits_value_repr (List.replicate e false ++ bs)
  rw [binaryScale_value] at h
  have hl : (List.replicate e false ++ bs).length = e + bs.length := by simp
  rw [hl] at h
  rw [binSyms_eq, h, List.map_append, List.map_replicate]

/-- The three constructed words and untouched block input satisfy shared setup. -/
theorem sharedInputBank_data {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : SharedInputReg → Fin T) (hrg : Function.Injective rg) (Lb n rows B : ℕ)
    (rowBits : List Bool) (hrows : Counter.value rowBits = rows)
    (hB : B < 2 ^ Lb) (hblock : R (rg .block) = binSyms Lb B) :
    ElementarySharedData (sharedInputConfig rg) Lb (n + rowBits.length) n B (rows * 2 ^ n)
      (sharedInputBank R rg n rows rowBits.length) := by
  have hfit : rows * 2 ^ n < 2 ^ (n + rowBits.length) := by
    have hr := Counter.value_lt rowBits
    rw [hrows] at hr
    have h := Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos n)
    simpa [pow_add, Nat.mul_comm] using h
  constructor
  · exact ⟨hB, by simp [sharedInputConfig, sharedInputBank, hrg.eq_iff, hblock]⟩
  · exact ⟨hfit, by simp [sharedInputConfig, sharedInputBank, hrg.eq_iff]⟩
  · simp [sharedInputConfig, sharedInputBank, hrg.eq_iff]
  · simp [sharedInputConfig, sharedInputBank]

def sharedInputPrivate {T : ℕ} (rg : SharedInputReg → Fin T) : List (Fin T) :=
  [rg .records, rg .field, rg .mask]

/-- Generation leaves all tapes outside its three output words unchanged. -/
theorem sharedInputBank_keep {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : SharedInputReg → Fin T) (n rows rowLength : ℕ) (j : Fin T)
    (hj : j ∉ sharedInputPrivate rg) :
    sharedInputBank R rg n rows rowLength j = R j := by
  have hrecords : j ≠ rg .records := by intro he; exact hj (by simp [sharedInputPrivate, he])
  have hfield : j ≠ rg .field := by intro he; exact hj (by simp [sharedInputPrivate, he])
  have hmask : j ≠ rg .mask := by intro he; exact hj (by simp [sharedInputPrivate, he])
  simp [sharedInputBank, hrecords, hfield, hmask]

/-- Raw shared-word cleanup preserves the routed stream and restores its inputs. -/
theorem sharedInput_restore {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : SharedInputReg → Fin T) (hrg : Function.Injective rg) (n rows rowLength : ℕ)
    (str : Fin T) (out : List (Fin (A + 4))) (hstr : str ∉ sharedInputPrivate rg)
    (hrecords : R (rg .records) = []) (hfield : R (rg .field) = []) (hmask : R (rg .mask) = []) :
    metadataCleared (Function.update (sharedInputBank R rg n rows rowLength) str out) (sharedInputPrivate rg) =
      Function.update R str out := by
  rw [metadataCleared_update _ _ _ _ hstr]
  congr 1
  funext j
  by_cases hr : j = rg .records
  · subst j; simp [sharedInputPrivate, metadataCleared, hrecords]
  · by_cases hf : j = rg .field
    · subst j; simp [sharedInputPrivate, metadataCleared, hrg.eq_iff, hfield]
    · by_cases hm : j = rg .mask
      · subst j; simp [sharedInputPrivate, metadataCleared, hrg.eq_iff, hmask]
      · simp [sharedInputPrivate, metadataCleared, sharedInputBank, hr, hf, hm]

theorem sharedInput_cleanCost {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : SharedInputReg → Fin T) (hrg : Function.Injective rg) (n rows rowLength : ℕ) :
    metadataCleanCost (sharedInputBank R rg n rows rowLength) (sharedInputPrivate rg) =
      6 * n + 2 * rowLength + 7 := by
  simp [sharedInputPrivate, metadataCleanCost, sharedInputBank, hrg.eq_iff]
  omega

end IntegerMultBounds.MathlibTM2.Routing
