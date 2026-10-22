module

public import IntegerMultBounds.MathlibTM2.Routing.ReadOffset
public import IntegerMultBounds.MathlibTM2.Host.IndexCode
public import IntegerMultBounds.MathlibTM2.Layer.CompactCodes

/-!
# Priced source-reading callbacks for modular rotations

The current source field is read through the fixed ordered descriptor interpreter.
Its compact offset and the current target field are then scanned by a wrap-class
code automaton. The offset is cleared afterwards. All stacks, including source,
descriptor and masks, are restored; only the code scan slot changes. The resulting
`CodeSpec` can be used directly by the existing record routing and merging passes.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-- Index fields and the fixed scratch bank of the source-reading callback. -/
inductive SourceReg (nf : ℕ) where
  | fld (f : Fin nf)
  | desc | mask | ts | tm | dst | g | off | spare (r : Fin 2) | st
  deriving DecidableEq

/-- Static input and empty scratch contents; field counters are supplied separately. -/
def sourceStatic (A G : ℕ) {nf W n : ℕ} (s : Fin n → Fin W) :
    SourceReg nf → List (Fin (A + 4))
  | .desc => (sourceTable (List.ofFn s)).flatten.map bitSymbol
  | .mask => binSyms (n * G) (maskVal n (fun j => j * G))
  | _ => []

/-- All callback data follows the current index, rather than a saved source header. -/
def SourceInv {T A nf W n : ℕ} (len : Fin nf → ℕ) (ι : SourceReg nf → Fin T)
    (G : ℕ) (s : Fin n → Fin W) (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  ∀ r, r ≠ .st → R (ι r) = match r with
    | .fld f => binSyms (len f) (digit len f i)
    | _ => sourceStatic A G s r

variable {T Q A nf W n G : ℕ} {U P : Type}

/-- The two input registers of the code automaton: current target, prepared offset. -/
def sourceCodeInputs (ι : SourceReg nf → Fin T) (ft : Fin nf) : Fin 2 → Fin T :=
  ![ι (.fld ft), ι .off]

/-- Read the current source, run the code automaton, then clear the compact offset. -/
def sourceCode (ι : SourceReg nf → Fin T) (fs ft : Fin nf) {nd : ℕ}
    (C : CAuto A 2 nd) : Pr P T Q A U :=
  .seq (readOffset (ι (.fld fs)) (ι .desc) (ι .ts) (ι .tm) (ι .dst) (ι .g)
    (ι .mask) (ι .off) (ι .st))
    (.seq (codePass (sourceCodeInputs ι ft) (fun r => ι (.spare r)) (ι .st) C)
      (bclear (ι .off)))

/-- The current arithmetic offset; all source positions are descriptor data. -/
def sourceValue (len : Fin nf → ℕ) (fs : Fin nf) (G : ℕ) (s : Fin n → Fin W) (i : ℕ) : ℕ :=
  placeVal n (fun j => j * G) (sourceBit s (digit len fs i))

/-- Callback cost includes interpretation, spreading, code scan and offset cleanup. -/
def sourceCodeCost (n W G : ℕ) : ℕ := n * (6 * W + 10) + 16 * (n * G) + 22

variable (body : P → Pr P T Q A U) {len : Fin nf → ℕ} {ι : SourceReg nf → Fin T}

/-- A concrete source-reading code program meets the full index-routing interface. -/
theorem sourceCode_spec (hι : Function.Injective ι) (fs ft : Fin nf)
    (hs : len fs = W) (ht : len ft = n * G) (hW : 0 < W) (hG : 0 < G)
    (s : Fin n → Fin W) {nd : ℕ} (C : CAuto A 2 nd) :
    CodeSpec body (sourceCode ι fs ft C) (fun f => ι (.fld f)) len (ι .st)
      (fun k => ∃ r, ι r = k) (SourceInv len ι G s) (codeSel C)
      (fun i => C.eval (n * G) ![digit len ft i, sourceValue len fs G s i])
      (sourceCodeCost n W G) where
  runs i v S hI := by
    have hne : ∀ {r r' : SourceReg nf}, r ≠ r' → ι r ≠ ι r' := fun h => hι.ne h
    have hr : [ι (.fld fs), ι .desc, ι .ts, ι .tm, ι .dst, ι .g].Nodup := by
      simp [hι.eq_iff]
    have hspread : GSRegs (ι .g) (ι .mask) (ι .ts) (ι .tm) (ι .dst) (ι .off) := by
      simp [GSRegs, hι.eq_iff]
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := readOffset_exec body (cs := ι .st) hr hspread
      (by simp [hι.eq_iff]) hW hG s (digit len fs i) v S
      (by simpa only [hs, binSyms_eq] using hI (.fld fs) (by simp))
      (hI .desc (by simp)) (by simpa [sourceStatic, binSyms_eq] using hI .mask (by simp))
      (hI .ts (by simp)) (hI .tm (by simp)) (hI .dst (by simp))
      (hI .g (by simp)) (hI .off (by simp))
    let offset := (binBits (n * G) (sourceValue len fs G s i)).map (bitSymbol (a := A))
    let R₁ := Function.update S.R (ι .off) offset
    have hlay : CodeLayout (sourceCodeInputs ι ft) (fun r => ι (.spare r)) (ι .st) := {
      rs_inj := by
        intro r r' he
        fin_cases r <;> fin_cases r' <;> simp_all [sourceCodeInputs, hι.eq_iff]
      tmps_inj := fun r r' he => by simpa using hι he
      rs_tmps := by intro r r'; fin_cases r <;> simp [sourceCodeInputs, hι.eq_iff]
      rs_st := by intro r; fin_cases r <;> simp [sourceCodeInputs, hι.eq_iff]
      tmps_st := by intro r; simp [hι.eq_iff] }
    obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := codePass_exec body hlay C (n * G)
      ![digit len ft i, sourceValue len fs G s i] v₁ { S with R := R₁ }
      (fun r => by
        fin_cases r
        · change R₁ (ι (.fld ft)) = _
          simp only [R₁, Function.update_of_ne (hne (show SourceReg.fld ft ≠ .off by simp))]
          simpa [ht] using hI (.fld ft) (by simp)
        · change R₁ (ι .off) = _
          simp [R₁, offset, binSyms_eq])
      (fun r => by
        change R₁ (ι (.spare r)) = _
        simp only [R₁, Function.update_of_ne (hne (show SourceReg.spare r ≠ .off by simp))]
        exact hI (.spare r) (by simp))
    obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := bclear_exec body (ι .off) v₂ { S with R := R₁ }
    have hlen : (R₁ (ι .off)).length = n * G := by simp [R₁, offset, binBits]
    have hfin : Function.update R₁ (ι .off) [] = S.R := by
      funext k
      by_cases hk : k = ι .off
      · subst k
        simpa [R₁, sourceStatic] using (hI .off (by simp)).symm
      · simp [R₁, hk]
    refine ⟨v₃, m₁ + ((6 * (n * G) + 4) + (2 * (R₁ (ι .off)).length + 2)),
      hu₃.trans (hu₂.trans hu₁), ?_, ?_, ?_⟩
    · rw [hlen]
      unfold sourceCodeCost
      omega
    · rw [hsc₃, hsc₂, codeSel_val]
      rfl
    · exact Exec.seq he₁ (Exec.seq he₂ (Exec.cast he₃ rfl (by rw [hfin])))
  cf_inj := fun f f' he => by simpa using hι he
  cf_Y := fun f => ⟨.fld f, rfl⟩
  digits := fun R i hI f => hI (.fld f) (by simp)
  frame := by
    intro R R' i hI hR r hr
    rw [hR (ι r) ⟨r, rfl⟩]
    exact hI r hr
  reidx := by
    intro R R' i j hI hfields hother r hr
    cases r <;> first
      | exact hfields _
      | contradiction
      | (rw [hother _ (fun f => hι.ne (by simp))]; exact hI _ (by simp))

end IntegerMultBounds.MathlibTM2.Routing
