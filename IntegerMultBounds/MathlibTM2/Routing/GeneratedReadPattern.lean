module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorTableCompile

/-! Generate an optional-pattern descriptor, interpret it, and erase it again.
Only the requested output changes; binary selector frames are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def generatedReadPattern {T Q A : ℕ} {P U : Type}
    (rg : BinaryMaskReg → Fin T) (selectors saved source desc ts tm dst out cs : Fin T) : Pr P T Q A U :=
  .seq (descriptorCompileProgram rg selectors saved desc)
    (.seq (readPattern source desc ts tm dst out cs) (bclear desc))

theorem generatedReadPattern_exec {T Q A W N : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (selectors saved source desc ts tm dst out cs : Fin T)
    (hss : selectors ≠ saved) (hsd : selectors ≠ desc) (had : saved ≠ desc)
    (hselectors : ∀ r, selectors ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hdesc : ∀ r, desc ≠ rg r)
    (hn : [source, desc, ts, tm, dst, out].Nodup)
    (L : ℕ) (hW : W + 1 < 2 ^ L) (s : Fin N → Option (Fin W)) (f : Fin W → Bool)
    (v : HS T Q A U) (S : Stacks T A) (hready : DescriptorCompileReady rg S.R L (W + 1))
    (hinput : S.R selectors = descriptorSelectorFrames L (List.ofFn (patternIndex s)).reverse)
    (hsave : S.R saved = []) (hd : S.R desc = [])
    (hsource : S.R source = (List.ofFn f).map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (descriptorCompileCallCost L (W + 1) + 2) + 2 * (N * (L + 1)) + 4 +
        (N * (6 * W + 14) + 8) + (2 * (N * (W + 1)) + 2) ∧
      Exec body (generatedReadPattern rg selectors saved source desc ts tm dst out cs) (mk v S) m
        (mk v' { S with R := Function.update S.R out ((List.ofFn (patternBit s f)).map bitSymbol ++ S.R out) }) := by
  have hsep : source ≠ desc ∧ ts ≠ desc ∧ tm ≠ desc ∧ dst ≠ desc ∧ out ≠ desc := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hn
    exact ⟨hn.1.1, Ne.symm hn.2.1.1, Ne.symm hn.2.1.2.1,
      Ne.symm hn.2.1.2.2.1, Ne.symm hn.2.1.2.2.2⟩
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := patternTableCompile_exec body rg hrg selectors saved desc
    hss hsd had hselectors hsaved hdesc L hW s v S hready hinput hsave
  let word := (patternTable s).flatten.map (bitSymbol (a := A))
  let S₁ : Stacks T A := { S with R := Function.update S.R desc word }
  have he₁' : Exec body (descriptorCompileProgram rg selectors saved desc) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hd, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := readPattern_exec body (cs := cs) hn s f v₁ S₁
    (by simpa [S₁, hsep.1] using hsource) (by simp [S₁, word])
    (by simpa [S₁, hsep.2.1] using hts) (by simpa [S₁, hsep.2.2.1] using htm)
    (by simpa [S₁, hsep.2.2.2.1] using hdst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R out ((List.ofFn (patternBit s f)).map bitSymbol ++ S₁.R out) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body desc v₂ S₂
  have hw : S₂.R desc = word := by simp [S₂, S₁, hsep.2.2.2.2.symm]
  have hlen : word.length = N * (W + 1) := by
    simp only [word, List.length_map, patternTable, sourceTable_size, List.length_ofFn]
  have hfinal : Function.update S₂.R desc [] = Function.update S.R out
      ((List.ofFn (patternBit s f)).map bitSymbol ++ S.R out) := by
    funext j
    by_cases hj : j = desc
    · subst j; simp [hd, hsep.2.2.2.2.symm]
    · by_cases ho : j = out
      · subst j; simp [S₂, S₁, hj]
      · simp [S₂, S₁, hj, ho]
  rw [hfinal, hw, hlen] at he₃
  exact ⟨v₃, m₁ + ((N * (6 * W + 14) + 8) + (2 * (N * (W + 1)) + 2)),
    hu₃.trans (hu₂.trans hu₁), by omega, Exec.seq he₁' (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
