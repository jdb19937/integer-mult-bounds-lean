module

public import IntegerMultBounds.Primes.PrimeTest
public import IntegerMultBounds.MathlibTM2.Fast.ParamSub

/-!
# Emitting the first primes of a window

`ptEmitC` on nine registers runs `ptNextC` (on registers `0 … 6`) `d` times and emits each
result. From `lo` in register `0` and `d` in register `8` it emits the first `d` primes above
`lo` in increasing order, in the format of the parameter program's source lengths:
`(pmEmitList A w (windowPrime lo) d).reverse` in front of the accumulator (`ptEmitC_do`). This is
the format of `pmEmitSC_do` with `windowPrime lo` in place of `modulus N x₀ a`.

When `(lo, hi]` holds at least `d` primes, every emitted prime lies in it
(`windowPrime_mem`), each search stays below `hi`, and the program uses at most
`ptEmitAtoms lo hi d` atoms with words `3 hi + 4 < 2^W`. Register `7` is the loop counter.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {A W w : ℕ}

/-- The next-prime registers inside the emitter. -/
def ptEmitReg : Fin 7 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6]

theorem ptEmitReg_injective : Function.Injective ptEmitReg := by decide

/-- Emit the first `d` primes above register `0`; register `8` holds `d`, `7` counts. -/
def ptEmitC : TblCode 9 := tblFor 7 8 (ptNextC.rename ptEmitReg ;; .ins (.emit 0 0))

/-- A bound on one search inside `(lo, hi]`. -/
def ptGapAtoms (lo hi : ℕ) : ℕ := 3 + ((hi - lo) * (3 + ptPrimeAtoms hi) + 2)

/-- The atoms of `ptEmitC`. -/
def ptEmitAtoms (lo hi d : ℕ) : ℕ := 1 + (d * ((ptGapAtoms lo hi + 1) + 1 + 2) + 2)

theorem le_iterate_nextPrimeAfter (lo j : ℕ) : lo ≤ nextPrimeAfter^[j] lo := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (lt_nextPrimeAfter _).le

theorem windowPrime_eq_iterate (lo j : ℕ) : windowPrime lo j = nextPrimeAfter^[j + 1] lo := rfl

/-- **The first `d` primes above `lo`.** From `lo` in register `0` and `d` in register `8`, when
`(lo, hi]` holds at least `d` primes and `3 hi + 4 < 2^W`, the program emits
`windowPrime lo 0, …, windowPrime lo (d - 1)`. -/
theorem ptEmitC_do (st : TblSt 9 A) {lo hi d : ℕ} (hlo : st.val 0 = lo) (hd : st.val 8 = d)
    (hcount : d ≤ ((Finset.Ioc lo hi).filter Nat.Prime).card) (hW : 3 * hi + 4 < 2 ^ W)
    (hdW : d < 2 ^ W) :
    TblDo A W w ptEmitC st (fun s => s.val 0 = nextPrimeAfter^[d] lo ∧ s.val 8 = d ∧
      s.acc = (pmEmitList A w (windowPrime lo) d).reverse ++ st.acc) (ptEmitAtoms lo hi d) := by
  refine TblDo.for d (ptGapAtoms lo hi + 1) hd hdW (by decide)
    (fun j s => s.val 0 = nextPrimeAfter^[j] lo ∧
      s.acc = (pmEmitList A w (windowPrime lo) j).reverse ++ st.acc)
    ⟨by simp [hlo], by simp [pmEmitList]⟩ ?_ ?_
  · rintro j hj s ⟨e0, ea⟩ e7 e8
    set c := nextPrimeAfter^[j] lo with hc
    have hwp : nextPrimeAfter c = windowPrime lo j := by
      rw [windowPrime_eq_iterate, Function.iterate_succ_apply']
    have hwhi : windowPrime lo j ≤ hi := windowPrime_le_of_card (by omega)
    have hclo : lo ≤ c := le_iterate_nextPrimeAfter lo j
    have hnext := TblDo.rename (f := ptEmitReg) ptEmitReg_injective
      (ptNextC_do (A := A) (W := W) (w := w) (s.restrict ptEmitReg) (x := c)
        (by simp [ptEmitReg, e0, hc]) (by rw [hwp]; omega))
    have hbound : ptNextAtoms c ≤ ptGapAtoms lo hi := by
      have hgap : nextPrimeAfter c - c ≤ hi - lo := by omega
      have hpa : ptPrimeAtoms (nextPrimeAfter c) ≤ ptPrimeAtoms hi :=
        ptPrimeAtoms_mono (by omega)
      have := Nat.mul_le_mul hgap (by omega : 1 + ptPrimeAtoms (nextPrimeAfter c) + 2 ≤
        3 + ptPrimeAtoms hi)
      unfold ptNextAtoms ptGapAtoms
      omega
    refine (hnext.seq (K₂ := 1) (fun s₁ ⟨⟨f0, _, fa⟩, hrest⟩ => TblDo.ins (.emit 0 0) ?_)).mono
      (fun _ h => h) (by omega)
    have f0' : s₁.val 0 = windowPrime lo j := by
      simpa [ptEmitReg, hwp] using f0
    have f7 : s₁.val 7 = j := by
      rw [hrest 7 (by intro y; fin_cases y <;> simp [ptEmitReg]), e7]
    have f8 : s₁.val 8 = d := by
      rw [hrest 8 (by intro y; fin_cases y <;> simp [ptEmitReg]), e8]
    have fa' : s₁.acc = s.acc := by simpa using fa
    refine ⟨by simp [TblIns.run, f7], by simp [TblIns.run, f8], ?_, ?_⟩
    · simp [TblIns.run, f0', windowPrime_eq_iterate]
    · simp [TblIns.run, f0', fa', ea, pmEmitList_succ, List.reverse_append]
  · rintro s ⟨e0, ea⟩ - e8
    exact ⟨e0, e8, ea⟩

end IntegerMultBounds.Primes
