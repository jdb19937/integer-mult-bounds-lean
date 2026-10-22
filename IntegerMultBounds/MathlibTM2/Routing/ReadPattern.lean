module

public import IntegerMultBounds.MathlibTM2.Routing.ReadOrdered
public import IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-!
# Source patterns with explicit zero entries

Each output position names a source bit or zero. A literal zero is temporarily
prefixed to the *metadata source word*, the fixed source-table interpreter runs,
and that prefix is removed. No physical borrowed address bit is initialized or
restricted. Source, descriptor and scan scratch are restored; the code is fixed.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-- Absent selectors request zero; present selectors request a physical source bit. -/
def patternBit {W L : ℕ} (s : Fin L → Option (Fin W)) (f : Fin W → Bool) (j : Fin L) : Bool :=
  (s j).elim false f

/-- The zero-prefixed source word has one actual zero at position zero. -/
def paddedBit {W : ℕ} (f : Fin W → Bool) : Fin (W + 1) → Bool := Fin.cases false f

def patternIndex {W L : ℕ} (s : Fin L → Option (Fin W)) (j : Fin L) : Fin (W + 1) :=
  (s j).elim 0 Fin.succ

def patternTable {W L : ℕ} (s : Fin L → Option (Fin W)) : List (List Bool) :=
  sourceTable (List.ofFn (patternIndex s))

/-- Descriptor interpretation produces exactly the requested pattern, in order. -/
theorem pattern_selection {W L : ℕ} (s : Fin L → Option (Fin W)) (f : Fin W → Bool) :
    (List.ofFn (patternIndex s)).map (paddedBit f) = List.ofFn (patternBit s f) := by
  rw [List.map_ofFn]
  congr 1
  funext j
  cases hs : s j <;> simp [patternIndex, paddedBit, patternBit, hs]

/-- Pattern bits extended by zero beyond the output width. -/
def patternBitNat {W L : ℕ} (s : Fin L → Option (Fin W)) (x j : ℕ) : Bool :=
  if hj : j < L then patternBit s (fun q => x.testBit q.val) ⟨j, hj⟩ else false

/-- The contiguous binary word described by a source pattern. -/
def patternValue {W L : ℕ} (s : Fin L → Option (Fin W)) (x : ℕ) : ℕ :=
  placeVal L id (patternBitNat s x)

theorem patternValue_lt {W L : ℕ} (s : Fin L → Option (Fin W)) (x : ℕ) :
    patternValue s x < 2 ^ L := placeVal_lt strictMono_id _ L

theorem patternValue_bits {W L : ℕ} (s : Fin L → Option (Fin W)) (x : ℕ) :
    binBits L (patternValue s x) = List.ofFn (patternBit s (fun q => x.testBit q.val)) := by
  unfold binBits
  congr 1
  funext j
  simp [patternValue, testBit_placeVal strictMono_id, patternBitNat, j.isLt]

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Prefix one literal zero to the metadata source register. -/
def zeroPrefix (src : Fin T) : Act T Q A U :=
  .push (.rt src) (fun _ => bitSymbol false) .done

/-- Remove the temporary metadata prefix without changing the host variables. -/
def dropPrefix (src : Fin T) : Act T Q A U := .pop (.rt src) (fun v _ => v) .done

/-- Interpret optional source selectors with one shared, explicitly priced zero bit. -/
def readPattern (src desc ts tm dst out cs : Fin T) : Pr P T Q A U :=
  .seq (.act (zeroPrefix src))
    (.seq (readRows src desc ts tm dst out cs) (.act (dropPrefix src)))

/-- Actual pattern execution: source, descriptor and scratch are restored. -/
theorem readPattern_exec {src desc ts tm dst out cs : Fin T}
    (h : [src, desc, ts, tm, dst, out].Nodup) {W L : ℕ}
    (s : Fin L → Option (Fin W)) (f : Fin W → Bool) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = (List.ofFn f).map bitSymbol)
    (hd : S.R desc = (patternTable s).flatten.map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (readPattern src desc ts tm dst out cs) (mk v S) (L * (6 * W + 14) + 8)
        (mk v' { S with
          R := Function.update S.R out ((List.ofFn (patternBit s f)).map bitSymbol ++ S.R out) }) := by
  have hn := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, _, _, _, _⟩ := hn
  let R₁ := Function.update S.R src (bitSymbol false :: S.R src)
  have hpush : (zeroPrefix src : Act T Q A U).run (mk v S) = mk v { S with R := R₁ } := by
    simp [zeroPrefix, Action.run, update_rt, R₁]
  obtain ⟨v₁, hu₁, he₁⟩ := readOrdered_exec body (cs := cs) h (Nat.zero_lt_succ W)
    (paddedBit f) (List.ofFn (patternIndex s)) v { S with R := R₁ }
    (by simp [R₁, paddedBit, List.ofFn_succ, hs])
    (by simpa [R₁, Ne.symm a1, patternTable] using hd)
    (by simp [R₁, Ne.symm a2, hts]) (by simp [R₁, Ne.symm a3, htm])
    (by simp [R₁, Ne.symm a4, hdst])
  rw [pattern_selection] at he₁
  let bits := (List.ofFn (patternBit s f)).map (bitSymbol (a := A)) ++ S.R out
  let R₂ := Function.update R₁ out bits
  have hout : R₁ out = S.R out := by simp [R₁, Ne.symm a5]
  dsimp only at he₁
  rw [hout] at he₁
  have hsrc : R₂ src = bitSymbol false :: S.R src := by simp [R₂, R₁, a5]
  have hrestore : Function.update R₂ src (S.R src) = Function.update S.R out bits := by
    funext k
    by_cases hk : k = src
    · subst k; simp [a5]
    · simp [R₂, R₁, Function.update_apply, hk]
  have hdrop : (dropPrefix src : Act T Q A U).run (mk v₁ { S with R := R₂ }) =
      mk v₁ { S with R := Function.update S.R out bits } := by
    simp only [dropPrefix, Action.run, mk_stk, mk_var, get_rt, hsrc, List.tail_cons]
    rw [update_rt]
    simp only [store_mk, hrestore]
  refine ⟨v₁, hu₁, Exec.cast (Exec.seq
    (hpush ▸ Exec.act (body := body) (zeroPrefix src) (mk v S))
    (Exec.seq he₁ (hdrop ▸ Exec.act (body := body) (dropPrefix src) (mk v₁ { S with R := R₂ }))))
      (by simp; ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
