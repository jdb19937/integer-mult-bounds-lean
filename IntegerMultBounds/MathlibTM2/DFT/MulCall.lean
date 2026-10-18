module

public import IntegerMultBounds.MathlibTM2.DFT.MulIO
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Fast.Glue

/-!
# The fast multiplier as a subroutine

`HostMultiplier κ` packages a host procedure table that multiplies every pair `(x, y)` from
`pairEnc (x, y)` on `.inp` to `encodeNat (x * y)` on `.out` within a time bound
`O(n (log n) ^ (1 - κ))` (`Fast.HostMulWithin`). The DFT development takes the multiplier as a
parameter, so it holds for every `κ` a multiplier achieves.

**The table.** The DFT machine runs on `M.T + D` registers, the multiplier's on the first `M.T`
(`M.emb D = Fin.castAdd D`), with local state `HS (M.T + D) M.Q M.A (M.U × B)`: the multiplier's
user component and the DFT's own `B`. `M.tab D B main` runs `main` at `none` and procedure `f` of
the multiplier at `some f`, embedded on its registers (`embProg`), lifted to the user state
`M.U × B` (`liftProg`, `splitUser`) and put on the host keys (`hostProg some`).

**The call.** `M.mulCall D B a b c t₁ … t₅` pushes `pairEnc (x, y)` onto `.inp` from registers
`a = binSyms La x` and `b = binSyms Lb y` (`pushNat`), resets the multiplier's part of the local
state to `M.v₀` keeping `B` (`setV₀`), calls the multiplier, and reads `.out` into the empty
register `c` as `binSyms (La + Lb) (x * y)` (`readProduct`). `mulCall_exec`: when `.inp`,
`.out`, every left stack and the multiplier's registers are empty, register `c` gains the product,
every other stack and the `B` component end as they started, in
`30 (La + Lb) + 4 |x y| + m + 63` steps with `m + 2 ≤ M.time (|x| + |y|)` (`|·|` the binary
length).
-/

@[expose] public section

open Turing Computability Asymptotics Filter IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

namespace IntegerMultBounds.MathlibTM2.DFT

/-! ### Stores with only `.inp` and `.out` -/

section IO

variable {T Q A : ℕ} {U : Type}

/-- Host stacks with `inp` and `out` and every register empty. -/
def ioStacks (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks T A :=
  ⟨inp, out, fun _ => [], fun _ => []⟩

theorem only_inp_eq (v : HS T Q A U) (l : List (Bool ⊕ Bool)) :
    Store.only (Γ := HΓ (T := T) A) v HK.inp l = mk v (ioStacks l []) :=
  Store.ext rfl (funext fun k => by cases k <;> rfl)

theorem only_out_eq (v : HS T Q A U) (o : List Bool) :
    Store.only (Γ := HΓ (T := T) A) v HK.out o = mk v (ioStacks [] o) :=
  Store.ext rfl (funext fun k => by cases k <;> rfl)

variable {T' : ℕ} {e : Fin T → Fin T'}

theorem embStk_io (S : Stacks T' A) (hL : ∀ i, S.L (e i) = []) (hR : ∀ i, S.R (e i) = []) :
    embStk e S = ioStacks S.inp S.out := by
  simp only [embStk, ioStacks]
  congr 1
  · funext i
    exact hL i
  · funext i
    exact hR i

theorem embExt_nil (S : Fin T' → List (Fin (A + 4))) (h : ∀ i, S (e i) = []) :
    embExt e (fun _ => []) S = S := by
  funext j
  unfold embExt
  cases hj : embInv e j with
  | none => rfl
  | some i =>
    obtain rfl := embInv_some hj
    exact (h i).symm

theorem embOvr_io (S : Stacks T' A) (hL : ∀ i, S.L (e i) = []) (hR : ∀ i, S.R (e i) = [])
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    embOvr e (ioStacks (T := T) inp out).get S = { S with inp := inp, out := out } := by
  simp only [embOvr, ioStacks, Stacks.get]
  rw [embExt_nil S.L hL, embExt_nil S.R hR]

end IO

theorem pairEnc_eq (x y : ℕ) :
    pairEnc (x, y) = (encodeNat x).map Sum.inl ++ (encodeNat y).map Sum.inr := rfl

/-! ### Host multipliers -/

/-- A host procedure table multiplying every pair within `time = O(n (log n) ^ (1 - κ))`. -/
structure HostMultiplier (κ : ℝ) where
  T : ℕ
  Q : ℕ
  A : ℕ
  U : Type
  P : Type
  fintypeU : Fintype U
  fintypeP : Fintype P
  body : P → Pr P T Q A U
  pm : P
  v₀ : HS T Q A U
  time : ℕ → ℕ
  run : ∀ x y, HostMulWithin body pm v₀ time x y
  isBigO : (fun n => (time n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - κ)

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- The multiplier's registers among `M.T + D`. -/
abbrev emb : Fin M.T → Fin (M.T + D) := Fin.castAdd D

theorem emb_injective : Function.Injective (M.emb D) := Fin.castAdd_injective _ _

/-- The procedure table: `main` at `none`, procedure `f` of the multiplier at `some f`. -/
def tab (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B)) :
    Option M.P → DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B)
  | none => main
  | some f => hostProg some (liftProg (splitUser B) id (embProg (M.emb D) id (M.body f)))

/-- The multiplier's part of the local state set to `v₀`; the `B` component is kept. -/
def setV₀ (w : HS (M.T + D) M.Q M.A (M.U × B)) : HS (M.T + D) M.Q M.A (M.U × B) :=
  withBuf (embUp (M.emb D) M.v₀ ((splitUser B) w).1) ((splitUser B) w).2

/-- Multiply register `a` by register `b` into the empty register `c`, through `t₁ … t₅`. -/
def mulCall (a b c t₁ t₂ t₃ t₄ t₅ : Fin (M.T + D)) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (pushNat b t₁ t₂ t₃ Sum.inr)) (.seq (hostCode (pushNat a t₁ t₂ t₃ Sum.inl))
    (.seq (.act (.load (M.setV₀ D B) .done)) (.seq (.call (some M.pm))
      (hostCode (readProduct c a b t₁ t₂ t₃ t₄ t₅)))))

/-- The multiplier runs on its registers of the big file, inside any `main`. -/
theorem call_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B)) (x y : ℕ)
    (w : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = pairEnc (x, y)) (hout : S.out = []) (hL : ∀ i, S.L (M.emb D i) = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (gi go : List Γ') :
    ∃ w' m, w'.user.2 = w.user.2 ∧ m + 2 ≤ M.time (pairEnc (x, y)).length ∧
      Exec (M.tab D B main) (.call (some M.pm)) (dmk (M.setV₀ D B w) S gi go) (m + 2)
        (dmk w' { S with inp := [], out := encodeNat (x * y) } gi go) := by
  obtain ⟨m, hm, h⟩ := M.run x y
  rw [only_inp_eq, only_out_eq] at h
  have hS : embStk (M.emb D) S = ioStacks (pairEnc (x, y)) [] := by
    rw [embStk_io S hL hR, hinp, hout]
  obtain ⟨v₁', -, -, h₁⟩ := exec_emb_ovr (M.emb_injective D) (ι := id)
    (body' := fun f => embProg (M.emb D) id (M.body f)) (fun _ => rfl) h
    (embUp (M.emb D) M.v₀ ((splitUser B) w).1) (embDn_up (M.emb_injective D) _ _) S hS
  rw [embOvr_io S hL hR] at h₁
  have h₂ := exec_lift (splitUser B) id
    (body' := fun f => liftProg (splitUser B) id (embProg (M.emb D) id (M.body f)))
    (fun _ => rfl) h₁ ((splitUser B) w).2
  have h₃ := exec_hostProg (ι := some) (body' := M.tab D B main) (fun _ => rfl) h₂ gi go
  exact ⟨withBuf v₁' ((splitUser B) w).2, m, rfl, hm, Exec.call h₃⟩

/-- `mulCall`: register `c` gains `binSyms (La + Lb) (x * y)`. -/
theorem mulCall_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {a b c t₁ t₂ t₃ t₄ t₅ : Fin (M.T + D)} (hreg : [c, a, b, t₁, t₂, t₃, t₄, t₅].Nodup)
    {La Lb x y : ℕ} (hx : x < 2 ^ La) (hy : y < 2 ^ Lb) (v : HS (M.T + D) M.Q M.A (M.U × B))
    (S : Stacks (M.T + D) M.A) (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ k, S.L k = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (ha : S.R a = binSyms La x) (hb : S.R b = binSyms Lb y)
    (hc : S.R c = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = [])
    (h₄ : S.R t₄ = []) (h₅ : S.R t₅ = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m, v'.user.2 = v.user.2 ∧
      m + 2 ≤ M.time (Nat.size x + Nat.size y) ∧
      Exec (M.tab D B main) (M.mulCall D B a b c t₁ t₂ t₃ t₄ t₅) (dmk v S gi go)
        (30 * (La + Lb) + 4 * Nat.size (x * y) + m + 63)
        (dmk v' { S with R := Function.update S.R c (binSyms (La + Lb) (x * y)) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  -- push `y`, then `x`
  obtain ⟨v₁, hu₁, e₁⟩ := pushNat_exec Empty.elim (s := b) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃)
    (by regs_nodup) Sum.inr hy v S hb h₁ h₂ h₃
  set S₁ : Stacks (M.T + D) M.A := { S with inp := (encodeNat y).map Sum.inr ++ S.inp } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := pushNat_exec Empty.elim (s := a) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃)
    (by regs_nodup) Sum.inl hx v₁ S₁ (by simp [hS₁, ha]) (by simp [hS₁, h₁])
    (by simp [hS₁, h₂]) (by simp [hS₁, h₃])
  set S₂ : Stacks (M.T + D) M.A := { S₁ with inp := (encodeNat x).map Sum.inl ++ S₁.inp }
    with hS₂
  have hS₂i : S₂.inp = pairEnc (x, y) := by simp [hS₂, hS₁, hinp, pairEnc_eq]
  -- reset the local state and call
  have e₃ : Exec (M.tab D B main) (.act (.load (M.setV₀ D B) .done)) (dmk v₂ S₂ gi go) 1
      (dmk (M.setV₀ D B v₂) S₂ gi go) := Exec.act _ _
  obtain ⟨w', m, hw', hm, e₄⟩ := M.call_exec D B main x y v₂ S₂ hS₂i (by simp [hS₂, hS₁, hout])
    (by simp [hS₂, hS₁, hL]) (by simpa [hS₂, hS₁] using hR) gi go
  set S₃ : Stacks (M.T + D) M.A := { S₂ with inp := [], out := encodeNat (x * y) } with hS₃
  -- read the product
  have hS₃a : S₃.R a = binSyms La x := by simp [hS₃, hS₂, hS₁, ha]
  have hS₃b : S₃.R b = binSyms Lb y := by simp [hS₃, hS₂, hS₁, hb]
  have hlen : ∀ L z, (binSyms (A := M.A) L z).length = L := fun L z => by simp [binSyms]
  have hz : x * y < 2 ^ ((S₃.R a).length + (S₃.R b).length) := by
    rw [hS₃a, hS₃b, hlen, hlen, pow_add]
    exact Nat.mul_lt_mul'' hx hy
  obtain ⟨v₅, hu₅, e₅⟩ := readProduct_exec Empty.elim hreg (z := x * y) w' S₃ hz
    (by simp [hS₃]) (by simp [hS₃, hS₂, hS₁, hc]) (by simp [hS₃, hS₂, hS₁, h₁])
    (by simp [hS₃, hS₂, hS₁, h₂]) (by simp [hS₃, hS₂, hS₁, h₃]) (by simp [hS₃, hS₂, hS₁, h₄])
    (by simp [hS₃, hS₂, hS₁, h₅])
  rw [hS₃a, hS₃b, hlen, hlen] at e₅
  have hsize : (pairEnc (x, y)).length = Nat.size x + Nat.size y := length_pairEnc x y
  refine ⟨v₅, m, ?_, hsize ▸ hm, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq (exec_hostCode e₂ gi go) (Exec.seq e₃ (Exec.seq e₄ (exec_hostCode e₅ gi go)))))
    (by ring) ?_⟩
  · rw [hu₅, hw']
    simp [setV₀, splitUser, withBuf, hu₂, hu₁]
  · show dmk v₅ _ gi go = dmk v₅ _ gi go
    congr 1
    simp [hS₃, hS₂, hS₁, hinp, hout]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
