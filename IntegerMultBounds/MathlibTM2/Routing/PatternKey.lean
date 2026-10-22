module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderRead
public import IntegerMultBounds.MathlibTM2.Node.KeyPass

/-!
# Executed destination-digit emission from live source descriptors

Build the actual source word from a header of current field counters, XOR it
with the target, emit the destination digit into the reverse key accumulator,
and clear the temporary word. All other registers are restored, including
configuration, the source/header, the full mask and every XOR temporary.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

variable {T Q A W L : ℕ} {P U : Type}

private theorem and_fullMask (x L : ℕ) (hx : x < 2 ^ L) : x &&& maskVal L id = x := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_and, testBit_maskVal strictMono_id]
  by_cases hq : q < L
  · simp [hq]
  · have hb : x.testBit q = false := Nat.testBit_eq_false_of_lt
      (hx.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hb]

def patternKey (fields : List (Fin T))
    (header desc ts tm dst word cy mask t0 t1 t2 acc st : Fin T) : Pr P T Q A U :=
  .seq (headerRead fields header desc ts tm dst word st)
    (.seq (xorF cy word mask t0 t1 t2 acc st) (bclear word))

theorem patternKey_exec (body : P → Pr P T Q A U) (fields : List (Fin T))
    {header desc ts tm dst word cy mask t0 t1 t2 acc st : Fin T}
    (hregs : [header, desc, ts, tm, dst, word, cy, mask, t0, t1, t2, acc].Nodup)
    (hst : st ∉ [cy, word, mask])
    (hfields : ∀ f ∈ fields, f ≠ header ∧ f ≠ ts ∧ f ≠ tm)
    (s : Fin L → Option (Fin W)) (x y : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hheader : S.R header = []) (hword : S.R word = [])
    (hsource : fields.flatMap S.R = binSyms W x)
    (hdesc : S.R desc = (patternTable s).flatten.map bitSymbol)
    (hy : S.R cy = binSyms L y) (hmask : S.R mask = binSyms L (maskVal L id))
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = [])
    (ht0 : S.R t0 = []) (ht1 : S.R t1 = []) (ht2 : S.R t2 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (patternKey fields header desc ts tm dst word cy mask t0 t1 t2 acc st)
        (mk v S)
        (sourceHeaderCost S.R fields + ((L * (6 * W + 14) + 8) + (2 * W + 2)) +
          ((9 * L + 8) + (2 * L + 2)))
        (mk v' { S with R := Function.update S.R acc ((binSyms L (y ^^^ patternValue s x)).reverse ++ S.R acc) }) := by
  have hn := hregs
  regs_ne hn
  have hr : [header, desc, ts, tm, dst, word].Nodup := by regs_nodup
  obtain ⟨v₁, hu₁, he₁⟩ := headerRead_exec body fields hr hfields s x v S
    hheader hsource hdesc hts htm hdst
  rw [hword, List.append_nil] at he₁
  let R₁ := Function.update S.R word (binSyms L (patternValue s x))
  have hk (r : Fin T) (hr : r ≠ word) : R₁ r = S.R r := by simp [R₁, hr]
  have hxregs : [cy, word, mask, t0, t1, t2, acc].Nodup := by regs_nodup
  obtain ⟨v₂, hu₂, he₂⟩ := xorF_exec body cy word mask t0 t1 t2 acc st hxregs hst
    L y (patternValue s x) (maskVal L id) v₁ { S with R := R₁ }
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact hy) (by simp [R₁])
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact hmask)
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact ht0)
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact ht1)
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact ht2)
  dsimp only at he₂
  rw [and_fullMask _ L (patternValue_lt s x), hk acc (by solve_by_elim)] at he₂
  let R₂ := Function.update R₁ acc ((binSyms L (y ^^^ patternValue s x)).reverse ++ S.R acc)
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body word v₂ { S with R := R₂ }
  have hlen : (R₂ word).length = L := by simp [R₂, R₁, *]
  have hrestore : Function.update R₂ word [] =
      Function.update S.R acc ((binSyms L (y ^^^ patternValue s x)).reverse ++ S.R acc) := by
    funext r
    by_cases hw : r = word
    · subst r; simp [*]
    by_cases ha : r = acc
    · subst r; simp [R₂, R₁, *]
    simp [R₂, R₁, hw, ha]
  dsimp only at he₃
  rw [hlen, hrestore] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
