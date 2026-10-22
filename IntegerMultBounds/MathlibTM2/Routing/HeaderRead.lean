module

public import IntegerMultBounds.MathlibTM2.Routing.SourceHeader
public import IntegerMultBounds.MathlibTM2.Routing.ReadPattern

/-!
# Executed pattern reading from a live field header

Copy current field words, interpret one optional-source descriptor, and clear the
header. Only the requested output changes; every field, descriptor and temporary
is restored. The exact bound includes header construction and clearing.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W L : ℕ} {P U : Type}

def headerRead (fields : List (Fin T)) (header desc ts tm dst out cs : Fin T) : Pr P T Q A U :=
  .seq (sourceHeader fields header ts tm)
    (.seq (readPattern header desc ts tm dst out cs) (bclear header))

theorem headerRead_exec (body : P → Pr P T Q A U) (fields : List (Fin T))
    {header desc ts tm dst out cs : Fin T}
    (hregs : [header, desc, ts, tm, dst, out].Nodup)
    (hfields : ∀ f ∈ fields, f ≠ header ∧ f ≠ ts ∧ f ≠ tm)
    (s : Fin L → Option (Fin W)) (x : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hheader : S.R header = []) (hword : fields.flatMap S.R = binSyms W x)
    (hdesc : S.R desc = (patternTable s).flatten.map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (headerRead fields header desc ts tm dst out cs) (mk v S)
        (sourceHeaderCost S.R fields + ((L * (6 * W + 14) + 8) + (2 * W + 2)))
        (mk v' { S with R := Function.update S.R out (binSyms L (patternValue s x) ++ S.R out) }) := by
  have hn := hregs
  regs_ne hn
  have htemp : [header, ts, tm].Nodup := by regs_nodup
  obtain ⟨v₁, hu₁, he₁⟩ := sourceHeader_exec body fields header ts tm hfields htemp v S hts htm
  rw [hheader, List.append_nil, hword] at he₁
  let R₁ := Function.update S.R header (binSyms W x)
  have hk (r : Fin T) (hr : r ≠ header) : R₁ r = S.R r := by simp [R₁, hr]
  obtain ⟨v₂, hu₂, he₂⟩ := readPattern_exec body hregs s (fun q => x.testBit q.val)
    v₁ { S with R := R₁ }
    (by simp [R₁, binSyms_eq, binBits])
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact hdesc)
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact hts)
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact htm)
    (by dsimp only; rw [hk _ (by solve_by_elim)]; exact hdst)
  dsimp only at he₂
  rw [← patternValue_bits, ← binSyms_eq, hk out (by solve_by_elim)] at he₂
  let R₂ := Function.update R₁ out (binSyms L (patternValue s x) ++ S.R out)
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body header v₂ { S with R := R₂ }
  have hlen : (R₂ header).length = W := by simp [R₂, R₁, *]
  have hrestore : Function.update R₂ header [] =
      Function.update S.R out (binSyms L (patternValue s x) ++ S.R out) := by
    funext r
    by_cases hr : r = header
    · subst r; simp [*]
    by_cases ho : r = out
    · subst r; simp [R₂, R₁, *]
    simp [R₂, R₁, hr, ho]
  dsimp only at he₃
  rw [hlen, hrestore] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
