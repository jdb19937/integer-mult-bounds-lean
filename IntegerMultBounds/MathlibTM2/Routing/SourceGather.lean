module

public import IntegerMultBounds.MathlibTM2.Routing.Coordinates
public import IntegerMultBounds.MathlibTM2.Node.CompactCode

/-!
# Priced source gathering for routing

Increasing source positions may be scattered anywhere in a source field. The
existing mask scanner gathers them, then spreads them to compact digit starts.
This supplies actual host execution and cleanup, not an offset oracle. Masks
and the source counter must already be present: their setup and subsequent
rotation passes are separate obligations. A nonmonotone source descriptor still
requires a proved reordering step; it cannot be passed to this theorem.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- The mask scanner reads exactly the source descriptor of the packed shear. -/
theorem gather_read {pos : ℕ → ℕ} (hpos : StrictMono pos) {n W : ℕ}
    (hW : ∀ j < n, pos j < W) (x : ℕ) :
    gatherL (binBits W x) (binBits W (maskVal n pos)) =
      (Coordinates.read (fun j : Fin n => pos j.val) x.testBit).map Packed.parity := by
  rw [Coordinates.read_parities]
  exact gatherL_mask hpos hW x

private theorem pack_ofFn (B : ℤ) {n : ℕ} (f : Fin n → ℤ) :
    IntegerMultBounds.Compact.Radix.pack B (List.ofFn f) =
      ∑ j : Fin n, f j * B ^ j.val := by
  induction n with
  | zero => simp [IntegerMultBounds.Compact.Radix.pack]
  | succ n ih =>
    rw [List.ofFn_succ, IntegerMultBounds.Compact.Radix.pack, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The prepared binary offset is exactly the radix-packed source list used by
`Packed.program`, not merely a list with the same number of bits. -/
theorem packed_read_eq (n G : ℕ) (pos : ℕ → ℕ) (x : ℕ) :
    IntegerMultBounds.Compact.Radix.pack ((2 : ℤ) ^ G)
      (Coordinates.read (fun j : Fin n => pos j.val) x.testBit) =
        (placeVal n (fun j => j * G) (fun j => x.testBit (pos j)) : ℤ) := by
  rw [Coordinates.read, pack_ofFn]
  unfold placeVal
  push_cast
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_mul]
  cases x.testBit (pos j.val) <;> simp [Nat.mul_comm]

/-- An actual source read, preserving the source, mask and every register except output. -/
theorem gather_read_exec {src mask ts tm dst out cs : Fin T}
    (h : GSRegs src mask ts tm dst out) {pos : ℕ → ℕ} (hpos : StrictMono pos)
    {n W : ℕ} (hW : ∀ j < n, pos j < W) (x : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hm : S.R mask = (binBits W (maskVal n pos)).map bitSymbol)
    (hs : S.R src = (binBits W x).map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * W + 8 ∧
      Exec body (gather src mask ts tm dst out cs) (mk v S) m
        (mk v' { S with
          R := Function.update S.R out
            (((Coordinates.read (fun j : Fin n => pos j.val) x.testBit).map Packed.parity).map
              bitSymbol ++ S.R out) }) := by
  obtain ⟨v', m, hu, hm', he⟩ := gather_exec body h
    (binBits W (maskVal n pos)) (binBits W x) (by simp [binBits])
    v S hm hs hts htm hdst
  rw [gather_read hpos hW x] at he
  exact ⟨v', m, hu, by simpa [binBits] using hm', he⟩

/-- Gather, spread to compact digit starts, and clear the gathered temporary. -/
def sourceOffset (src mA mB g s ts tm dst cs : Fin T) : Pr P T Q A U :=
  .seq (gsProg src mA mB g s ts tm dst cs) (bclear g)

/-- Physical offset preparation with explicit cost and restored gather scratch.
The output `s` is the only changed register. The source positions need not be
regularly spaced; the compact destination positions have spacing `G`. -/
theorem sourceOffset_exec {src mA mB g s ts tm dst cs : Fin T}
    (h₁ : GSRegs src mA ts tm dst g) (h₂ : GSRegs g mB ts tm dst s)
    {pos : ℕ → ℕ} (hpos : StrictMono pos) {n W G : ℕ} (hG : 0 < G)
    (hW : ∀ j < n, pos j < W) (x : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = (binBits W x).map bitSymbol)
    (ha : S.R mA = (binBits W (maskVal n pos)).map bitSymbol)
    (hb : S.R mB = (binBits (n * G) (maskVal n (fun j => j * G))).map bitSymbol)
    (hg : S.R g = []) (hs0 : S.R s = [])
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 8 * W + 8 * (n * G) + 2 * n + 18 ∧
      Exec body (sourceOffset src mA mB g s ts tm dst cs) (mk v S) m
        (mk v' { S with
          R := Function.update S.R s
            ((binBits (n * G) (placeVal n (fun j => j * G)
              (fun j => x.testBit (pos j)))).map bitSymbol) }) := by
  have hmono : StrictMono (fun j : ℕ => j * G) := fun _ _ h =>
    Nat.mul_lt_mul_of_pos_right h hG
  have hbound : ∀ j < n, j * G < n * G := fun _ h =>
    Nat.mul_lt_mul_of_pos_right h hG
  have hread := gatherL_mask hpos hW x
  have hspread := spreadL_mask hmono hbound (fun j => x.testBit (pos j))
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := gsProg_exec (body := body) (cs := cs) h₁ h₂
    (binBits W x) (binBits W (maskVal n pos))
    (binBits (n * G) (maskVal n (fun j => j * G)))
    (by simp [binBits])
    (by rw [hread, count_maskVal hmono hbound]; simp)
    v S hs ha hb hg hs0 hts htm hdst
  rw [hread, hspread] at he₁
  let bits := (List.ofFn fun j : Fin n => x.testBit (pos j)).map
    (bitSymbol (a := A))
  let offset := (binBits (n * G)
    (placeVal n (fun j => j * G) (fun j => x.testBit (pos j)))).map (bitSymbol (a := A))
  let R₁ := Function.update (Function.update S.R g bits) s offset
  have hgs : g ≠ s := by
    have h := h₂
    simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at h
    exact h.1.2.2.2.2
  obtain ⟨v₂, hu₂, _, he₂⟩ := bclear_exec body g v₁ { S with R := R₁ }
  have hlen : (R₁ g).length = n := by simp [R₁, hgs, bits]
  have hrestore : Function.update R₁ g [] = Function.update S.R s offset := by
    funext k
    by_cases hk : k = g
    · subst k; simp [hgs, hg]
    · simp [R₁, Function.update_apply, hk]
  refine ⟨v₂, m₁ + (2 * (R₁ g).length + 2), hu₂.trans hu₁, ?_, ?_⟩
  · simp only [binBits, List.length_ofFn] at hm₁
    rw [hlen]
    omega
  · change Exec body (.seq _ _) _ _ _
    exact Exec.seq he₁ (Exec.cast he₂ rfl (by rw [hrestore]))

end IntegerMultBounds.MathlibTM2.Routing
