module

public import IntegerMultBounds.MathlibTM2.Node.UDiv
public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXor

/-!
# The layout parameters of a compact slot XOR

A node holding the slot width `L = K k`, the offset `a₀`, the column count `k` and the digit
width `G` in unary registers computes the positions of the control fields: with `H = (k - 1) G`
the width of a control field, the borrow field starts at `bB = a₀ - H`, just below the slots,
and the chunk distances are `pT = (m L - 1) / H + 2` and `pU = pT + 1`, which put `T` at
`bB + pT H ∈ [a₀ + m L, a₀ + m L + H)` and `U` one chunk higher (`cxParams`, `cxParams_exec`).
`cxLayout` is the data of the slot XOR with these positions; it is valid (`cxLayout_valid`)
when `H ≤ a₀` and `a₀ + m L + 3 H ≤ n`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

set_option linter.unusedSimpArgs false

/-- The registers of the layout computation: the inputs `a₀ L k G`, the outputs `bB pT pU` and
six scratch registers. -/
inductive PrmReg where
  | a₀ | L | k | G | bB | pT | pU | t₁ | t₂ | t₃ | t₄ | t₅ | t₆
  deriving DecidableEq

section Params

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- The layout parameters: from `k`, `G`, `a₀`, `L`, the registers `bB`, `pT`, `pU` gain
`a₀ - (k - 1) G`, `(mm L - 1) / ((k - 1) G) + 2` and one more tick. -/
noncomputable def cxParams (mm : ℕ) (ι : PrmReg → Fin T) : Pr P T Q A U :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (ucopy (ι .k) (ι .t₁) (ι .t₂))
    (.act (popTop (ι .t₁))))
    (umulU (ι .t₁) (ι .G) (ι .t₂) (ι .t₃) (ι .t₄)))
    (ucopy (ι .a₀) (ι .bB) (ι .t₃)))
    (usub (ι .t₂) (ι .bB) (ι .t₃)))
    (umul mm (ι .L) (ι .t₃) (ι .t₄)))
    (.act (popTop (ι .t₃))))
    (udivU (ι .t₃) (ι .t₂) (ι .pT) (ι .t₄) (ι .t₅) (ι .t₆)))
    (.act (pushN (ι .pT) (fun _ => tick) 2 .done)))
    (ucopy (ι .pT) (ι .pU) (ι .t₄)))
    (.act (pushN (ι .pU) (fun _ => tick) 1 .done)))
    (uclear (ι .t₁))) (.seq (uclear (ι .t₂)) (uclear (ι .t₃)))

/-- Sequencing a register division. -/
lemma cx_then_udivU {p : Pr P T Q A U}
    {s : IntegerMultBounds.MathlibTM2.Stack.Store (HΓ (T := T) A) (HS T Q A U)} {m : ℕ}
    {v₁ : HS T Q A U} {S₁ : Stacks T A} (he : Exec body p s m (mk v₁ S₁)) {a b q c t₂ t₃ : Fin T}
    (hreg : [a, b, q, c, t₂, t₃].Nodup) (hb : 1 ≤ (S₁.R b).length) (hc : S₁.R c = [])
    (ht₂ : S₁.R t₂ = []) (ht₃ : S₁.R t₃ = []) :
    ∃ (v₂ : HS T Q A U) (m₂ : ℕ), v₂.user = v₁.user ∧
      m₂ ≤ 12 * ((S₁.R a).length + (S₁.R b).length) + 12 ∧
      Exec body (.seq p (udivU a b q c t₂ t₃)) s (m + m₂)
        (mk v₂ { S₁ with
          R := Function.update S₁.R q
            (List.replicate ((S₁.R a).length / (S₁.R b).length) tick ++ S₁.R q) }) := by
  obtain ⟨v₂, m₂, hu, hm, he₂⟩ := udivU_exec body hreg v₁ S₁ hb hc ht₂ ht₃
  exact ⟨v₂, m₂, hu, hm, Exec.seq he he₂⟩

/-- Sequencing a push of `c` ticks. -/
lemma cx_then_pushN {p : Pr P T Q A U}
    {s : IntegerMultBounds.MathlibTM2.Stack.Store (HΓ (T := T) A) (HS T Q A U)} {m : ℕ}
    {v₁ : HS T Q A U} {S₁ : Stacks T A} (he : Exec body p s m (mk v₁ S₁)) (r : Fin T) (c : ℕ) :
    Exec body (.seq p (.act (pushN r (fun _ => tick) c .done))) s (m + 1)
      (mk v₁ { S₁ with R := Function.update S₁.R r (List.replicate c tick ++ S₁.R r) }) := by
  have h := Exec.seq he (Exec.act (body := body) (pushN r (fun _ => tick) c .done) (mk v₁ S₁))
  rwa [pushN_run, run_done] at h

variable {ι : PrmReg → Fin T}

set_option hygiene false in
macro "pne" : tactic => `(tactic| exact hι.ne (by decide))

set_option hygiene false in
macro "psimp" : tactic => `(tactic|
  simp [Function.update_of_ne, hι.eq_iff, ha₀, hL, hk, hG, hbB, hpT, hpU, h1, h2, h3, h4, h5, h6,
    List.tail_replicate, List.drop_replicate, List.replicate_append_replicate])

set_option hygiene false in
macro "psimp" "at" h:ident : tactic => `(tactic|
  simp [Function.update_of_ne, hι.eq_iff, ha₀, hL, hk, hG, hbB, hpT, hpU, h1, h2, h3, h4, h5, h6,
    List.tail_replicate, List.drop_replicate, List.replicate_append_replicate] at $h:ident ⊢)

set_option maxHeartbeats 1000000 in
/-- **The layout parameters.** -/
theorem cxParams_exec (mm : ℕ) (hι : Function.Injective ι) {a₀ L k G : ℕ}
    (hH : 1 ≤ (k - 1) * G) (v : HS T Q A U) (S : Stacks T A)
    (ha₀ : (S.R (ι .a₀)).length = a₀) (hL : (S.R (ι .L)).length = L)
    (hk : (S.R (ι .k)).length = k) (hG : (S.R (ι .G)).length = G)
    (hbB : S.R (ι .bB) = []) (hpT : S.R (ι .pT) = []) (hpU : S.R (ι .pU) = [])
    (h1 : S.R (ι .t₁) = []) (h2 : S.R (ι .t₂) = []) (h3 : S.R (ι .t₃) = [])
    (h4 : S.R (ι .t₄) = []) (h5 : S.R (ι .t₅) = []) (h6 : S.R (ι .t₆) = []) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ 20 * (a₀ + k * G + k + L + mm * L + (k - 1) * G) + 60 ∧
      Exec body (cxParams mm ι) (mk v S) m (mk v' { S with R := R' }) ∧
      R' (ι .bB) = List.replicate (a₀ - (k - 1) * G) tick ∧
      R' (ι .pT) = List.replicate ((mm * L - 1) / ((k - 1) * G) + 2) tick ∧
      R' (ι .pU) = List.replicate ((mm * L - 1) / ((k - 1) * G) + 3) tick ∧
      ∀ t, t ≠ ι .bB → t ≠ ι .pT → t ≠ ι .pU → R' t = S.R t := by
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := ι .k) (b := ι .t₁) (t := ι .t₂) (by pne) (by pne)
    (by pne) v S h2
  have he₂ := cx_then_popTop body he₁ (ι .t₁)
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := cx_then_umulU body he₂ (a := ι .t₁) (b := ι .G) (c := ι .t₂)
    (t₁ := ι .t₃) (t₂ := ι .t₄) (by simp [List.nodup_cons, hι.eq_iff]) (by psimp) (by psimp)
  obtain ⟨v₄, hu₄, he₄⟩ := sx_then_ucopy body he₃ (a := ι .a₀) (b := ι .bB) (t := ι .t₃)
    (by pne) (by pne) (by pne) (by psimp)
  obtain ⟨v₅, hu₅, he₅⟩ := sx_then_usub body he₄ (a := ι .t₂) (b := ι .bB) (t := ι .t₃)
    (by pne) (by pne) (by pne) (by psimp)
  obtain ⟨v₆, hu₆, he₆⟩ := sx_then_umul body he₅ mm (a := ι .L) (b := ι .t₃) (t := ι .t₄)
    (by pne) (by pne) (by pne) (by psimp)
  have he₇ := cx_then_popTop body he₆ (ι .t₃)
  obtain ⟨v₈, m₈, hu₈, hm₈, he₈⟩ := cx_then_udivU body he₇ (a := ι .t₃) (b := ι .t₂)
    (q := ι .pT) (c := ι .t₄) (t₂ := ι .t₅) (t₃ := ι .t₆) (by simp [List.nodup_cons, hι.eq_iff])
    (by psimp; omega) (by psimp) (by psimp) (by psimp)
  have he₉ := cx_then_pushN body he₈ (ι .pT) 2
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := sx_then_ucopy body he₉ (a := ι .pT) (b := ι .pU) (t := ι .t₄)
    (by pne) (by pne) (by pne) (by psimp)
  have he₁₁ := cx_then_pushN body he₁₀ (ι .pU) 1
  obtain ⟨v₁₂, hu₁₂, he₁₂⟩ := sx_then_uclear body he₁₁ (ι .t₁)
  obtain ⟨v₁₃, hu₁₃, he₁₃⟩ := uclear_exec body (ι .t₂) v₁₂ _
  obtain ⟨v₁₄, hu₁₄, he₁₄⟩ := uclear_exec body (ι .t₃) v₁₃ _
  refine ⟨v₁₄, _, _, by rw [hu₁₄, hu₁₃, hu₁₂, hu₁₀, hu₈, hu₆, hu₅, hu₄, hu₃, hu₁], ?_,
    Exec.seq he₁₂ (Exec.seq he₁₃ he₁₄), ?_, ?_, ?_, ?_⟩
  · psimp at hm₃
    psimp at hm₈
    have hq : (mm * L - 1) / ((k - 1) * G) ≤ mm * L := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    have hkG : (k - 1) * G ≤ k * G := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hkG' : (k - 1) * (4 * G + 9) ≤ 4 * (k * G) + 9 * k :=
      calc (k - 1) * (4 * G + 9) ≤ k * (4 * G + 9) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = 4 * (k * G) + 9 * k := by ring
    have hmL : mm * L - 1 ≤ mm * L := Nat.sub_le _ _
    have hk1 : k - 1 ≤ k := Nat.sub_le _ _
    omega
  · psimp
  · psimp <;> rfl
  · psimp <;> rfl
  · intro t hbB' hpT' hpU'
    by_cases e1 : t = ι .t₁
    · subst e1; psimp
    by_cases e2 : t = ι .t₂
    · subst e2; psimp
    by_cases e3 : t = ι .t₃
    · subst e3; psimp
    by_cases e4 : t = ι .t₄
    · subst e4; psimp
    by_cases e5 : t = ι .t₅
    · subst e5; psimp
    by_cases e6 : t = ι .t₆
    · subst e6; psimp
    simp [Function.update_of_ne, hbB', hpT', hpU', e1, e2, e3, e4, e5, e6]

end Params

/-! ### The layout -/

/-- The data of the slot XOR of `x` into `y` with the control fields placed by `cxParams`. -/
def cxLayout (mm a₀ K ρ L R n rw k G x y : ℕ) : CxD :=
  ⟨a₀, K, ρ, L, R, n, rw, k, G, a₀ - (k - 1) * G, (mm * L - 1) / ((k - 1) * G) + 2,
    (mm * L - 1) / ((k - 1) * G) + 3, x, y⟩

/-- The layout is valid when a control field fits below the slots and three fit above. -/
theorem cxLayout_valid {mm a₀ K ρ L R n rw k G x y : ℕ} (hρ : ρ < K) (hLK : L = K * k)
    (hk : 2 ≤ k) (hR : 1 ≤ R) (hrw : 1 ≤ rw) (hxy : x ≠ y) (hx : x < mm) (hy : y < mm)
    (hG : 1 ≤ G) (hGK : G + 3 ≤ K) (hfront : (k - 1) * G ≤ a₀)
    (hback : a₀ + mm * L + 3 * ((k - 1) * G) ≤ n) :
    (cxLayout mm a₀ K ρ L R n rw k G x y).Valid := by
  have hH1 : 1 ≤ (k - 1) * G := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdm := Nat.div_add_mod (mm * L - 1) ((k - 1) * G)
  have hmod := Nat.mod_lt (mm * L - 1) (by omega : 0 < (k - 1) * G)
  have hq1 : (k - 1) * G * ((mm * L - 1) / ((k - 1) * G)) ≤ mm * L - 1 := by omega
  have hq2 : mm * L - 1 < (k - 1) * G * ((mm * L - 1) / ((k - 1) * G)) + (k - 1) * G := by omega
  clear hdm hmod
  have hhi : (max x y + 1) * L ≤ mm * L := Nat.mul_le_mul_right _ (by have := max_lt hx hy; omega)
  unfold cxLayout
  generalize (mm * L - 1) / ((k - 1) * G) = q at *
  generalize hHdef : (k - 1) * G = H at *
  have e2 : (q + 2) * H = H * q + 2 * H := by ring
  have e3 : (q + 3) * H = H * q + 3 * H := by ring
  refine ⟨hρ, hLK, hk, hR, hrw, hxy, hG, hGK, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ q + 2
    omega
  · show q + 2 < q + 3
    omega
  · show a₀ - H + (k - 1) * G ≤ a₀ + min x y * L
    rw [hHdef]
    omega
  · show a₀ + (max x y + 1) * L ≤ a₀ - H + (q + 2) * ((k - 1) * G)
    rw [hHdef, e2]
    omega
  · show a₀ - H + (q + 3) * ((k - 1) * G) + (k - 1) * G ≤ n
    rw [hHdef, e3]
    omega

end IntegerMultBounds.MathlibTM2.Node
