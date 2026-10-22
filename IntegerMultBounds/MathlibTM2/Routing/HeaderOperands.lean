module

public import IntegerMultBounds.MathlibTM2.Routing.PatternOperands
public import IntegerMultBounds.MathlibTM2.Routing.SourceHeader

/-!
# Live-header callback execution

Build the metadata source from actual live counters, run the concrete two-pattern
callback, then clear the header. The complete execution restores every stack;
its cost includes header construction and cleanup as well as both pattern scans.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W L : ℕ} {P U : Type}

def headerPatternCode (fields : List (Fin T)) (ι : PatternReg 2 → Fin T)
    {nd : ℕ} (C : CAuto A 3 nd) : Pr P T Q A U :=
  .seq (sourceHeader fields (ι (.fld 0)) (ι .ts) (ι .tm))
    (.seq (patternCode ι 0 1 C) (bclear (ι (.fld 0))))

/-- A complete callback, including the previously separate source-header work.
The header-word equation concerns the actual live source tapes. -/
theorem headerPatternCode_exec (body : P → Pr P T Q A U)
    (fields : List (Fin T)) (ι : PatternReg 2 → Fin T) (hι : Function.Injective ι)
    (hfields : ∀ f ∈ fields, f ≠ ι (.fld 0) ∧ f ≠ ι .ts ∧ f ≠ ι .tm)
    (s : Fin 2 → Fin L → Option (Fin W)) {nd : ℕ} (C : CAuto A 3 nd)
    (x y : ℕ) (hx : x < 2 ^ W) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hheader : S.R (ι (.fld 0)) = [])
    (hword : fields.flatMap S.R = binSyms W x)
    (htgt : S.R (ι (.fld 1)) = binSyms L y)
    (hscratch : ∀ r : PatternReg 2, (∀ f, r ≠ .fld f) → r ≠ .st →
      S.R (ι r) = patternStatic A s r) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ sourceHeaderCost S.R fields + (patternCodeCost L W + (2 * W + 2)) ∧
      codeSel C (v'.scan (ι .st)).val =
        C.eval L ![y, patternValue (s 0) x, patternValue (s 1) x] ∧
      Exec body (headerPatternCode fields ι C) (mk v S) m (mk v' S) := by
  have hne : ∀ {r r' : PatternReg 2}, r ≠ r' → ι r ≠ ι r' := fun h => hι.ne h
  obtain ⟨v₁, hu₁, he₁⟩ := sourceHeader_exec body fields (ι (.fld 0)) (ι .ts) (ι .tm)
    hfields (by simp [hι.eq_iff]) v S
    (hscratch .ts (by simp) (by simp)) (hscratch .tm (by simp) (by simp))
  rw [hheader, List.append_nil, hword] at he₁
  let R₁ := Function.update S.R (ι (.fld 0)) (binSyms W x)
  obtain ⟨v₂, m₂, hu₂, hm₂, hc₂, he₂⟩ := patternOperands_exec body ι hι s C x y hx hy
    v₁ { S with R := R₁ } (by simp [R₁])
    (by simpa [R₁, hι.eq_iff] using htgt)
    (fun r hr hs => by
      change R₁ (ι r) = _
      rw [show R₁ (ι r) = S.R (ι r) by simp [R₁, hne (hr 0)]]
      exact hscratch r hr hs)
  obtain ⟨v₃, hu₃, hscan₃, he₃⟩ := bclear_exec body (ι (.fld 0)) v₂ { S with R := R₁ }
  have hlen : (R₁ (ι (.fld 0))).length = W := by simp [R₁]
  have hrestore : Function.update R₁ (ι (.fld 0)) [] = S.R := by
    funext k
    by_cases hk : k = ι (.fld 0)
    · subst k; simp [hheader]
    · simp [R₁, hk]
  refine ⟨v₃, sourceHeaderCost S.R fields + (m₂ + (2 * W + 2)),
    hu₃.trans (hu₂.trans hu₁), Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _, ?_, ?_⟩
  · simpa only [hscan₃] using hc₂
  · exact Exec.seq he₁ (Exec.seq he₂ (Exec.cast he₃ (by rw [hlen])
      (by rw [hrestore])))

end IntegerMultBounds.MathlibTM2.Routing
