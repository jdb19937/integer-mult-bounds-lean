module

public import IntegerMultBounds.MathlibTM2.DFT.Trunc
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The host parts of a Hensel round

A round of the Hensel iteration for `-p⁻¹` modulo a power of two lifts `y` from `k` bits to
`2 k` bits by `y ↦ (2 y + p y²) mod 2 ^ (2k)`. Between its two products, which call the fast
multiplier, it runs these host procedures:

* `bcopyLow s wR d t₁ t₂`: `d` gains the low `|wR|` bits of `s` on top and `s` is kept
  (`bcopyLow_exec`, `6 m + 6` steps for `|wR| = m`): the top `m` symbols of `s` move onto `t₁`
  (`moveTop`, `scanR`), and draining `t₁` pushes each symbol back onto `s` and onto `d`
  (`dupTo`, `drainR`).
* `henselA W K K2 pW P2 t₁ t₂`: `W` loses `|K|` symbols (`usub`), `K2 := K ++ K`, and
  `P2 := binSyms (k + k) p` from `pW` (`henselA_exec`, `28 k + 22` steps).
* `henselC Y K K2 P2 Z Ur Yn cnt t₁ t₂`: from `Ur` holding `X` in `k + k + k` bits and `Y` holding
  `y` in `k` bits, `Y := (X mod 2 ^ (k+k) + 2 y) mod 2 ^ (k+k)` in `k + k` bits and `K := K2`;
  `Z`, `P2`, `Ur`, `K2` end empty (`henselC_exec`, at most `120 k + 80` steps).
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### Copying the low part -/

/-- Push `sym` onto register `s` and onto register `d`, then continue with `k`. -/
def dupTo (s d : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .push (.rt s) (fun v => v.sym.getD blank) (.push (.rt d) (fun v => v.sym.getD blank) k)

/-- The effect of `dupTo s d` with symbol `x`. -/
def dupToFx (s d : Fin T) : Fin (A + 4) → (Fin T → List (Fin (A + 4))) →
    Fin T → List (Fin (A + 4)) :=
  fun x R => Function.update (Function.update R s (x :: R s)) d (x :: R d)

lemma regFx_dupTo {s d : Fin T} (hsd : s ≠ d) :
    RegFx (dupTo (T := T) (Q := Q) (A := A) (U := U) s d) (dupToFx s d) := by
  intro x k v S hx
  refine ⟨v, rfl, ?_⟩
  simp [dupTo, dupToFx, Action.run, hx, update_rt, Function.update_of_ne hsd.symm]

lemma frame_dupTo {a s d : Fin T} (has : a ≠ s) (had : a ≠ d) :
    Frame a (dupToFx (A := A) s d) := by
  intro x R l
  simp only [dupToFx, Function.update_of_ne has.symm, Function.update_of_ne had.symm]
  rw [Function.update_comm has, Function.update_comm had]

lemma foldl_dupTo {s d : Fin T} (hsd : s ≠ d) :
    ∀ (l : List (Fin (A + 4))) (R : Fin T → List (Fin (A + 4))),
      l.foldl (fun R x => dupToFx s d x R) R =
        Function.update (Function.update R s (l.reverse ++ R s)) d (l.reverse ++ R d)
  | [], R => by simp
  | x :: rest, R => by
      simp only [List.foldl_cons]
      rw [foldl_dupTo hsd rest]
      funext k
      simp only [dupToFx, Function.update_apply]
      split_ifs <;> simp_all

/-- Copy the low `|wR|` bits of `s` onto `d`, keeping `s`. -/
def bcopyLow (s wR d t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR wR t₂ (moveTop s t₁)) (drainR t₁ (dupTo s d))

/-- `bcopyLow`: `d` gains `binSyms m X` from `s = binSyms (m + e) X`, for `|wR| = m`. -/
theorem bcopyLow_exec {s wR d t₁ t₂ : Fin T} (hreg : [s, wR, d, t₁, t₂].Nodup) {m e X : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hs : S.R s = binSyms (m + e) X)
    (hw : (S.R wR).length = m) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bcopyLow s wR d t₁ t₂) (mk v S) (6 * m + 6)
        (mk v' { S with R := Function.update S.R d (binSyms m X ++ S.R d) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := scanR_exec' body ‹wR ≠ t₂› (regFx_moveTop ‹s ≠ t₁›)
    (frame_moveTop ‹s ≠ wR›.symm ‹wR ≠ t₁›) (frame_moveTop ‹s ≠ t₂›.symm ‹t₁ ≠ t₂›.symm) v S h₂
  rw [foldl_moveTop ‹s ≠ t₁› _ _ (by rw [hs, hw]; simp), hw, hs, binSyms_append,
    List.drop_left' (length_binSyms m X), List.take_left' (length_binSyms m X), h₁,
    List.append_nil] at e₁
  set S₁ : Stacks T A := { S with
    R := Function.update (Function.update S.R s (binSyms e (X / 2 ^ m))) t₁
      (binSyms m X).reverse } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := drainR_exec body t₁ (regFx_dupTo ‹s ≠ d›)
    (frame_dupTo ‹s ≠ t₁›.symm ‹d ≠ t₁›.symm) v₁ S₁
  have hS₁t : S₁.R t₁ = (binSyms m X).reverse := by simp [hS₁]
  rw [hS₁t, foldl_dupTo ‹s ≠ d›, List.length_reverse, length_binSyms,
    List.reverse_reverse] at e₂
  have hsX : binSyms m X ++ binSyms e (X / 2 ^ m) = S.R s := by rw [hs, binSyms_append]
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) ?_⟩
  clear e₁ e₂
  simp only [hS₁]
  congr 2
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### The first part of a round -/

/-- `W` loses `|K|` symbols, `K2 := K ++ K`, and `P2` gains the low `|K2|` bits of `pW`. -/
def henselA (W K K2 pW P2 t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (usub K W t₁) (.seq (bcopy K K2 t₁ t₂) (.seq (bcopy K K2 t₁ t₂)
    (bcopyLow pW K2 P2 t₁ t₂)))

/-- `henselA`: `W := W.drop k`, `K2 := K ++ K`, `P2 := binSyms (k + k) p`. -/
theorem henselA_exec {W K K2 pW P2 t₁ t₂ : Fin T} (hreg : [W, K, K2, pW, P2, t₁, t₂].Nodup)
    {k e p : ℕ} (v : HS T Q A U) (S : Stacks T A) (hK : (S.R K).length = k)
    (hpW : S.R pW = binSyms (k + k + e) p) (hK2 : S.R K2 = []) (hP2 : S.R P2 = [])
    (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (henselA W K K2 pW P2 t₁ t₂) (mk v S) (28 * k + 22)
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R W ((S.R W).drop k)) K2
            (S.R K ++ S.R K)) P2 (binSyms (k + k) p) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := usub_exec body ‹W ≠ K›.symm ‹K ≠ t₁› ‹W ≠ t₁› v S h₁
  rw [hK] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R W ((S.R W).drop k) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bcopy_exec body (a := K) (c := K2) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁ S₁ (by simp [hS₁, ‹W ≠ t₁›.symm, h₁]) (by simp [hS₁, ‹W ≠ t₂›.symm, h₂])
  rw [show S₁.R K = S.R K by simp [hS₁, ‹W ≠ K›.symm], hK,
    show S₁.R K2 = [] by simp [hS₁, ‹W ≠ K2›.symm, hK2], List.append_nil] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R K2 (S.R K) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := K) (c := K2) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₂ S₂ (by simp [hS₂, hS₁, ‹K2 ≠ t₁›.symm, ‹W ≠ t₁›.symm, h₁])
    (by simp [hS₂, hS₁, ‹K2 ≠ t₂›.symm, ‹W ≠ t₂›.symm, h₂])
  rw [show S₂.R K = S.R K by simp [hS₂, hS₁, ‹K ≠ K2›, ‹W ≠ K›.symm], hK,
    show S₂.R K2 = S.R K by simp [hS₂]] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R K2 (S.R K ++ S.R K) } with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := bcopyLow_exec body (s := pW) (wR := K2) (d := P2) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (m := k + k) (e := e) (X := p) v₃ S₃
    (by simp [hS₃, hS₂, hS₁, ‹K2 ≠ pW›.symm, ‹W ≠ pW›.symm, hpW])
    (by simp [hS₃, hK]) (by simp [hS₃, hS₂, hS₁, ‹K2 ≠ t₁›.symm, ‹W ≠ t₁›.symm, h₁])
    (by simp [hS₃, hS₂, hS₁, ‹K2 ≠ t₂›.symm, ‹W ≠ t₂›.symm, h₂])
  rw [show S₃.R P2 = [] by simp [hS₃, hS₂, hS₁, ‹K2 ≠ P2›.symm, ‹W ≠ P2›.symm, hP2],
    List.append_nil] at e₄
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂
    (Exec.seq e₃ e₄))) (by ring) ?_⟩
  clear e₁ e₂ e₃ e₄
  simp only [hS₃, hS₂, hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### The last part of a round -/

/-- `Y := (Ur mod 2 ^ (k+k) + 2 Y) mod 2 ^ (k+k)`, `K := K2`, and the work registers cleared. -/
def henselC (Y K K2 P2 Z Ur Yn cnt t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (btrunc Ur K2 t₁ t₂) (.seq (bclear Z) (.seq (bclear P2) (.seq (bwiden Y K2 cnt t₁ t₂)
    (.seq (bshift Y t₁ fun _ => bitSymbol false) (.seq (badd Ur Y Yn t₁ t₂ cnt Yn)
      (.seq (bclear Ur) (.seq (bclear Y) (.seq (bcopy Yn Y t₁ t₂) (.seq (bclear Yn)
        (.seq (bclear K) (.seq (bcopy K2 K t₁ t₂) (bclear K2))))))))))))

/-- `henselC`: `Y := binSyms (k + k) ((X mod 2 ^ (k+k) + 2 y) mod 2 ^ (k+k))`, `K := K2`. -/
theorem henselC_exec {Y K K2 P2 Z Ur Yn cnt t₁ t₂ : Fin T}
    (hreg : [Y, K, K2, P2, Z, Ur, Yn, cnt, t₁, t₂].Nodup) {k X y z q : ℕ} (hk : 1 ≤ k)
    (hy : y < 2 ^ k) (v : HS T Q A U) (S : Stacks T A) (hU : S.R Ur = binSyms (k + k + k) X)
    (hY : S.R Y = binSyms k y) (hZ : S.R Z = binSyms (k + k) z)
    (hP2 : S.R P2 = binSyms (k + k) q) (hK2 : (S.R K2).length = k + k)
    (hK : (S.R K).length = k) (hYn : S.R Yn = []) (hc : S.R cnt = []) (h₁ : S.R t₁ = [])
    (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ 120 * k + 80 ∧
      Exec body (henselC Y K K2 P2 Z Ur Yn cnt t₁ t₂) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update S.R Z []) P2 []) Ur []) Y
              (binSyms (k + k) ((X % 2 ^ (k + k) + 2 * y) % 2 ^ (k + k)))) K (S.R K2))
            K2 [] }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hkk : k ≤ k + k := by omega
  have h2y : 2 * y < 2 ^ (k + k) := by
    calc 2 * y < 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring
      _ ≤ 2 ^ (k + k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hXm : X % 2 ^ (k + k) < 2 ^ (k + k) := Nat.mod_lt _ (by positivity)
  -- `Ur := X mod 2 ^ (k+k)`
  obtain ⟨v₁, hu₁, e₁⟩ := btrunc_exec body (a := Ur) (wR := K2) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := k + k) (e := k) (X := X) v S hU hK2 h₁ h₂
  rw [← binSyms_mod (k + k) X] at e₁
  set S₁ : Stacks T A :=
    { S with R := Function.update S.R Ur (binSyms (k + k) (X % 2 ^ (k + k))) } with hS₁
  -- clear `Z`, `P2`
  obtain ⟨v₂, hu₂, -, e₂⟩ := bclear_exec body Z v₁ S₁
  rw [show S₁.R Z = binSyms (k + k) z by simp [hS₁, ‹Z ≠ Ur›, hZ], length_binSyms] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R Z [] } with hS₂
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec body P2 v₂ S₂
  rw [show S₂.R P2 = binSyms (k + k) q by simp [hS₂, hS₁, ‹P2 ≠ Z›, ‹P2 ≠ Ur›, hP2],
    length_binSyms] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R P2 [] } with hS₃
  -- `Y := 2 y` in `k + k` bits
  obtain ⟨v₄, hu₄, e₄⟩ := bwiden_exec body (a := Y) (wR := K2) (cnt := cnt) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) hkk hy v₃ S₃ (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R Y (binSyms (k + k) y) } with hS₄
  obtain ⟨v₅, hu₅, e₅⟩ := bshift_exec body (s := Y) (t := t₁) ‹Y ≠ t₁› (fun _ => bitSymbol false)
    v₄ S₄ (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  beta_reduce at e₅
  rw [show S₄.R Y = binSyms (k + k) y by simp [hS₄], length_binSyms, binSyms_shift,
    Bool.toNat_false, Nat.add_zero] at e₅
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R Y (binSyms (k + k) (2 * y)) }
    with hS₅
  -- `Yn := Ur + Y`
  obtain ⟨v₆, hu₆, -, -, e₆⟩ := badd_exec body (a := Ur) (b := Y) (c := Yn) (tx := t₁) (ty := t₂)
    (tz := cnt) (cy := Yn) (by regs_nodup) ‹Ur ≠ Yn›.symm ‹Y ≠ Yn›.symm hXm h2y v₅ S₅
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₅])
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  rw [show S₅.R Yn = [] by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm], List.append_nil] at e₆
  set y' := (X % 2 ^ (k + k) + 2 * y) % 2 ^ (k + k) with hy'
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R Yn (binSyms (k + k) y') } with hS₆
  -- clear `Ur`, `Y`; `Y := Yn`; clear `Yn`
  obtain ⟨v₇, hu₇, -, e₇⟩ := bclear_exec body Ur v₆ S₆
  rw [show S₆.R Ur = binSyms (k + k) (X % 2 ^ (k + k)) by
    simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm], length_binSyms] at e₇
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R Ur [] } with hS₇
  obtain ⟨v₈, hu₈, -, e₈⟩ := bclear_exec body Y v₇ S₇
  rw [show S₇.R Y = binSyms (k + k) (2 * y) by simp [hS₇, hS₆, hS₅, *, Ne.symm],
    length_binSyms] at e₈
  set S₈ : Stacks T A := { S₇ with R := Function.update S₇.R Y [] } with hS₈
  obtain ⟨v₉, hu₉, e₉⟩ := bcopy_exec body (a := Yn) (c := Y) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₈ S₈ (by simp [hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  rw [show S₈.R Yn = binSyms (k + k) y' by simp [hS₈, hS₇, hS₆, *, Ne.symm],
    show S₈.R Y = [] by simp [hS₈], List.append_nil, length_binSyms] at e₉
  set S₉ : Stacks T A := { S₈ with R := Function.update S₈.R Y (binSyms (k + k) y') } with hS₉
  obtain ⟨v₁₀, hu₁₀, -, e₁₀⟩ := bclear_exec body Yn v₉ S₉
  rw [show S₉.R Yn = binSyms (k + k) y' by simp [hS₉, hS₈, hS₇, hS₆, *, Ne.symm],
    length_binSyms] at e₁₀
  set S₁₀ : Stacks T A := { S₉ with R := Function.update S₉.R Yn [] } with hS₁₀
  -- `K := K2`
  obtain ⟨v₁₁, hu₁₁, -, e₁₁⟩ := bclear_exec body K v₁₀ S₁₀
  rw [show (S₁₀.R K).length = k by
    simp [hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]] at e₁₁
  set S₁₁ : Stacks T A := { S₁₀ with R := Function.update S₁₀.R K [] } with hS₁₁
  obtain ⟨v₁₂, hu₁₂, e₁₂⟩ := bcopy_exec body (a := K2) (c := K) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁₁ S₁₁
    (by simp [hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  have hS₁₁K2 : S₁₁.R K2 = S.R K2 := by
    simp [hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]
  rw [hS₁₁K2, hK2, show S₁₁.R K = [] by simp [hS₁₁], List.append_nil] at e₁₂
  set S₁₂ : Stacks T A := { S₁₁ with R := Function.update S₁₁.R K (S.R K2) } with hS₁₂
  obtain ⟨v₁₃, hu₁₃, -, e₁₃⟩ := bclear_exec body K2 v₁₂ S₁₂
  rw [show S₁₂.R K2 = S.R K2 by simp [hS₁₂, ‹K ≠ K2›.symm, hS₁₁K2], hK2] at e₁₃
  refine ⟨v₁₃, _, by rw [hu₁₃, hu₁₂, hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁],
    ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ (Exec.seq e₁₁
        (Exec.seq e₁₂ e₁₃)))))))))))) rfl ?_⟩
  · omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    simp only [hS₁₂, hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
    clear hS₁₂ hS₁₁ hS₁₀ hS₉ hS₈ hS₇ hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hS₁₁K2 hy' h2y hXm hkk hk hy hU hY
      hZ hP2 hK2 hK hc h₁ h₂ hreg
    congr 2
    funext j
    by_cases hjK2 : j = K2
    · subst hjK2; simp
    by_cases hjK : j = K
    · subst hjK; simp [hjK2]
    by_cases hjY : j = Y
    · subst hjY; simp [*, Ne.symm]
    by_cases hjU : j = Ur
    · subst hjU; simp [*, Ne.symm]
    by_cases hjYn : j = Yn
    · subst hjYn; simp [*, Ne.symm]
    by_cases hjZ : j = Z
    · subst hjZ; simp [*, Ne.symm]
    by_cases hjP : j = P2
    · subst hjP; simp [*, Ne.symm]
    simp [*]

end IntegerMultBounds.MathlibTM2.DFT
