module

public import IntegerMultBounds.MathlibTM2.DFT.MulCall
public import IntegerMultBounds.MathlibTM2.DFT.RedcTail
public import IntegerMultBounds.MathlibTM2.DFT.Reduction
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Montgomery reduction with the fast multiplier

The DFT registers are `M.dreg D j = Fin.natAdd M.T j`, after the multiplier's (`emb_eq_dreg`:
the two never meet).

`M.redcProg D B tR pR qR wR oR m1 m2 sR t₁ … t₅` computes Montgomery's REDC for `R = 2 ^ r`:

1. `m1 := t p'` (`mulCall`), then `m1 := t p' mod 2 ^ r` (`btrunc` by the width register `wR`);
2. `m2 := m1 · p` (`mulCall`);
3. `redcTail`: `oR := (t + m2) / 2 ^ r`, minus `p` if not below `p`; `m1`, `m2` cleared.

`redc_exec`: for `0 < p`, `2 p ≤ 2 ^ r`, `2 ^ r ∣ p p' + 1`, `p' < 2 ^ r` and `t < p 2 ^ r`, with
`tR = binSyms (r + r) t`, `pR = binSyms r p`, `qR = binSyms r p'` and `|wR| = r`, register `oR`
ends with `binSyms r (redc p (2 ^ r) p' t)` and every other stack as it started, in at most
`250 r + 200 + m₁ + m₂` steps, where `m₁ + 2`, `m₂ + 2` are bounded by the multiplier's time on
the two products.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- The DFT registers, after the multiplier's. -/
abbrev dreg (j : Fin D) : Fin (M.T + D) := Fin.natAdd M.T j

@[simp] theorem emb_eq_dreg (i : Fin M.T) (j : Fin D) : M.emb D i = M.dreg D j ↔ False := by
  refine iff_false_intro fun h => ?_
  have h' := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h'
  have := i.isLt
  omega

@[simp] theorem dreg_inj (j k : Fin D) : M.dreg D j = M.dreg D k ↔ j = k :=
  ⟨fun h => Fin.ext (by have h' := congrArg Fin.val h; simpa using h'), fun h => h ▸ rfl⟩

theorem nodup_dreg {l : List (Fin D)} (h : l.Nodup) : (l.map (M.dreg D)).Nodup :=
  List.Nodup.map (fun _ _ e => (M.dreg_inj D _ _).1 e) h

/-- Montgomery's REDC on the DFT registers. -/
def redcProg (tR pR qR wR oR m1 m2 sR t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.mulCall D B (M.dreg D tR) (M.dreg D qR) (M.dreg D m1) (M.dreg D t₁) (M.dreg D t₂)
      (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
    (.seq (hostCode (btrunc (M.dreg D m1) (M.dreg D wR) (M.dreg D t₁) (M.dreg D t₂)))
      (.seq (M.mulCall D B (M.dreg D m1) (M.dreg D pR) (M.dreg D m2) (M.dreg D t₁)
          (M.dreg D t₂) (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
        (hostCode (redcTail (M.dreg D tR) (M.dreg D pR) (M.dreg D wR) (M.dreg D oR)
          (M.dreg D m1) (M.dreg D m2) (M.dreg D sR) (M.dreg D t₁) (M.dreg D t₂)
          (M.dreg D t₃)))))

theorem redc_eq_redcOut (p r p' t : ℕ) :
    redc p (2 ^ r) p' t = redcOut p r (t + t * p' % 2 ^ r * p) := by
  simp only [redc, redcRaw, redcDigit, redcOut, Nat.mod_mul_mod]

/-- `redcProg`: `oR := binSyms r (redc p (2 ^ r) p' t)`. -/
theorem redc_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {tR pR qR wR oR m1 m2 sR t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [tR, pR, qR, wR, oR, m1, m2, sR, t₁, t₂, t₃, t₄, t₅].Nodup)
    {r p p' t : ℕ} (hp : 0 < p) (hpr : 2 * p ≤ 2 ^ r) (hp'r : p' < 2 ^ r) (ht : t < p * 2 ^ r)
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ k, S.L k = [])
    (hR : ∀ i, S.R (M.emb D i) = [])
    (htR : S.R (M.dreg D tR) = binSyms (r + r) t) (hpR : S.R (M.dreg D pR) = binSyms r p)
    (hqR : S.R (M.dreg D qR) = binSyms r p') (hwR : (S.R (M.dreg D wR)).length = r)
    (hoR : S.R (M.dreg D oR) = []) (hm1 : S.R (M.dreg D m1) = [])
    (hm2 : S.R (M.dreg D m2) = []) (hsR : S.R (M.dreg D sR) = [])
    (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = [])
    (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m₁ m₂ n, v'.user.2 = v.user.2 ∧
      m₁ + 2 ≤ M.time (Nat.size t + Nat.size p') ∧
      m₂ + 2 ≤ M.time (Nat.size (t * p' % 2 ^ r) + Nat.size p) ∧
      n ≤ 250 * r + 200 + m₁ + m₂ ∧
      Exec (M.tab D B main) (M.redcProg D B tR pR qR wR oR m1 m2 sR t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update S.R (M.dreg D oR) (binSyms r (redc p (2 ^ r) p' t)) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  -- arithmetic
  have hpr' : p < 2 ^ r := by omega
  have h2r : (2 : ℕ) ^ (r + r) = 2 ^ r * 2 ^ r := pow_add 2 r r
  have ht2 : t < 2 ^ (r + r) := by
    rw [h2r]; exact ht.trans_le (Nat.mul_le_mul_right _ hpr'.le)
  have hm : t * p' % 2 ^ r < 2 ^ r := Nat.mod_lt _ (by positivity)
  set m := t * p' % 2 ^ r with hm_def
  have hq : m * p < 2 ^ (r + r) := by rw [h2r]; exact Nat.mul_lt_mul'' hm hpr'
  have hsum : t + m * p < 2 ^ (r + r) := by
    have hmp : m * p < 2 ^ r * p := Nat.mul_lt_mul_of_pos_right hm hp
    calc t + m * p < p * 2 ^ r + 2 ^ r * p := Nat.add_lt_add ht hmp
      _ = 2 * p * 2 ^ r := by ring
      _ ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul_right _ hpr
      _ = 2 ^ (r + r) := h2r.symm
  have hraw : (t + m * p) / 2 ^ r < 2 ^ r := Nat.div_lt_of_lt_mul (by rw [← h2r]; exact hsum)
  have htp : t * p' < 2 ^ (r + r + r) := by
    rw [pow_add]; exact Nat.mul_lt_mul'' ht2 hp'r
  -- 1. `m1 := t p'`
  obtain ⟨v₁, m₁, hu₁, hm₁, e₁⟩ := M.mulCall_exec D B main (a := M.dreg D tR)
    (b := M.dreg D qR) (c := M.dreg D m1) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa using hnd [m1, tR, qR, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) ht2 hp'r v S hinp hout
    hL hR htR hqR hm1 h₁ h₂ h₃ h₄ h₅ gi go
  set S₁ : Stacks (M.T + D) M.A :=
    { S with R := Function.update S.R (M.dreg D m1) (binSyms (r + r + r) (t * p')) } with hS₁
  -- `m1 := t p' mod 2 ^ r`
  obtain ⟨v₂, hu₂, e₂⟩ := btrunc_exec Empty.elim (a := M.dreg D m1) (wR := M.dreg D wR)
    (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa using hnd [m1, wR, t₁, t₂] (by regs_nodup)) (r := r) (e := r + r) (X := t * p')
    v₁ S₁ (by rw [show r + (r + r) = r + r + r by ring]; simp [hS₁])
    (by simp [hS₁, ‹wR ≠ m1›, hwR]) (by simp [hS₁, ‹m1 ≠ t₁›.symm, h₁])
    (by simp [hS₁, ‹m1 ≠ t₂›.symm, h₂])
  rw [← binSyms_mod r (t * p'), ← hm_def] at e₂
  set S₂ : Stacks (M.T + D) M.A := { S₁ with R := Function.update S₁.R (M.dreg D m1) (binSyms r m) }
    with hS₂
  -- 2. `m2 := m p`
  obtain ⟨v₃, m₂, hu₃, hm₂, e₃⟩ := M.mulCall_exec D B main (a := M.dreg D m1)
    (b := M.dreg D pR) (c := M.dreg D m2) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa using hnd [m2, m1, pR, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hm hpr' v₂ S₂
    (by simp [hS₂, hS₁, hinp]) (by simp [hS₂, hS₁, hout]) (by simp [hS₂, hS₁, hL])
    (by intro i; simp [hS₂, hS₁, hR]) (by simp [hS₂])
    (by simp [hS₂, hS₁, ‹pR ≠ m1›, hpR]) (by simp [hS₂, hS₁, ‹m1 ≠ m2›.symm, hm2])
    (by simp [hS₂, hS₁, ‹m1 ≠ t₁›.symm, h₁]) (by simp [hS₂, hS₁, ‹m1 ≠ t₂›.symm, h₂])
    (by simp [hS₂, hS₁, ‹m1 ≠ t₃›.symm, h₃]) (by simp [hS₂, hS₁, ‹m1 ≠ t₄›.symm, h₄])
    (by simp [hS₂, hS₁, ‹m1 ≠ t₅›.symm, h₅]) gi go
  set S₃ : Stacks (M.T + D) M.A :=
    { S₂ with R := Function.update S₂.R (M.dreg D m2) (binSyms (r + r) (m * p)) } with hS₃
  -- 3. the tail
  obtain ⟨v₄, n₄, hu₄, hn₄, e₄⟩ := redcTail_exec Empty.elim (tR := M.dreg D tR)
    (pR := M.dreg D pR) (wR := M.dreg D wR) (oR := M.dreg D oR) (m1 := M.dreg D m1)
    (m2 := M.dreg D m2) (sR := M.dreg D sR) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃)
    (by simpa using hnd [tR, pR, wR, oR, m1, m2, sR, t₁, t₂, t₃] (by regs_nodup))
    ht2 hq hsum hraw hpr' v₃ S₃
    (by simp [hS₃, hS₂, hS₁, ‹tR ≠ m1›, ‹tR ≠ m2›, htR]) (by simp [hS₃])
    (by simp [hS₃, hS₂, hS₁, ‹pR ≠ m1›, ‹pR ≠ m2›, hpR])
    (by simp [hS₃, hS₂, hS₁, ‹wR ≠ m1›, ‹wR ≠ m2›, hwR])
    (by simp [hS₃, hS₂, hS₁, ‹oR ≠ m1›, ‹oR ≠ m2›, hoR])
    (by simp [hS₃, hS₂, hS₁, ‹m1 ≠ sR›.symm, ‹m2 ≠ sR›.symm, hsR])
    (by simp [hS₃, hS₂, hS₁, ‹m1 ≠ t₁›.symm, ‹m2 ≠ t₁›.symm, h₁])
    (by simp [hS₃, hS₂, hS₁, ‹m1 ≠ t₂›.symm, ‹m2 ≠ t₂›.symm, h₂])
    (by simp [hS₃, hS₂, hS₁, ‹m1 ≠ t₃›.symm, ‹m2 ≠ t₃›.symm, h₃])
  have hS₃m1 : (S₃.R (M.dreg D m1)).length = r := by
    simp [hS₃, hS₂, ‹m1 ≠ m2›]
  rw [hS₃m1] at hn₄
  have hsz₁ : Nat.size (t * p') ≤ r + r + r := Nat.size_le.2 htp
  have hsz₂ : Nat.size (m * p) ≤ r + r := Nat.size_le.2 hq
  refine ⟨v₄, m₁, m₂, _, ?_, hm₁, hm₂, ?_, Exec.cast (Exec.seq e₁ (Exec.seq (exec_hostCode e₂ gi go)
    (Exec.seq e₃ (exec_hostCode e₄ gi go)))) rfl ?_⟩
  · rw [hu₄, hu₃, hu₂, hu₁]
  · omega
  · clear e₁ e₂ e₃ e₄
    show dmk v₄ _ gi go = dmk v₄ _ gi go
    rw [redc_eq_redcOut, ← hm_def]
    congr 1
    simp only [hS₃, hS₂, hS₁]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
