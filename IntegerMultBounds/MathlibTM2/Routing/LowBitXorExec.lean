module

public import IntegerMultBounds.MathlibTM2.Routing.LowBitXorCode
public import IntegerMultBounds.MathlibTM2.Host.Radix

/-!
# Executed elementary XOR on the lowest address bit

The source position is supplied by its binary mask, not compiled into the
program. The existing route/merge machine restores all registers except the
record stream and has the same scan cost as a single-bit layout move.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

/-- Prepared elementary scan bank with an arbitrary outer row count. -/
structure ElementarySharedCfg {T A t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (R : Fin T → List (Fin (A + 4))) (n M B a : ℕ) : Prop where
  r0 : R (rg .r0) = []
  r1 : R (rg .r1) = []
  r2 : R (rg .r2) = []
  r3 : R (rg .r3) = []
  q0 : R (rg .q0) = []
  q1 : R (rg .q1) = []
  q2 : R (rg .q2) = []
  q3 : R (rg .q3) = []
  tmp : R (rg .tmp) = []
  ctrB : (R (rg .ctrB)).length = B
  cnt : (R (rg .cnt)).length = M
  fld : R (rg .fld) = binSyms n 0
  mA : R (rg .mA) = binSyms n (2 ^ a)
  us : ∀ r, R (rg (.us r)) = []

structure ElementaryCfg {T A t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (R : Fin T → List (Fin (A + 4))) (n M B a b : ℕ) : Prop
    extends ElementarySharedCfg rg R n M B a where
  mB : R (rg .mB) = binSyms n (2 ^ b)

theorem ElementarySharedCfg.congr {T A t₀ : ℕ} {rg : LayReg t₀ → Fin T}
    {R R' : Fin T → List (Fin (A + 4))} {n M B a : ℕ}
    (hcfg : ElementarySharedCfg rg R n M B a)
    (hkeep : ∀ r, r ≠ .str → r ≠ .mB → (∀ j, r ≠ .sw j) → R' (rg r) = R (rg r)) :
    ElementarySharedCfg rg R' n M B a := by
  cases hcfg
  constructor <;> simp_all

theorem ElementarySharedCfg.update_stream {T A t₀ : ℕ} {rg : LayReg t₀ → Fin T}
    (hrg : Function.Injective rg) {R : Fin T → List (Fin (A + 4))} {n M B a : ℕ}
    (hcfg : ElementarySharedCfg rg R n M B a) (out : List (Fin (A + 4))) :
    ElementarySharedCfg rg (Function.update R (rg .str) out) n M B a := by
  apply hcfg.congr
  intro r hr _ _
  exact Function.update_of_ne (fun he => hr (hrg he)) _ _

theorem ElementaryCfg.update_stream {T A t₀ : ℕ} {rg : LayReg t₀ → Fin T}
    (hrg : Function.Injective rg) {R : Fin T → List (Fin (A + 4))} {n M B a b : ℕ}
    (hcfg : ElementaryCfg rg R n M B a b) (out : List (Fin (A + 4))) :
    ElementaryCfg rg (Function.update R (rg .str) out) n M B a b := by
  refine ⟨hcfg.toElementarySharedCfg.update_stream hrg out, ?_⟩
  simpa [hrg.eq_iff] using hcfg.mB

def elementaryScanCost (n M B : ℕ) : ℕ := M * (18 * B + 20 * n + 36) + 8 * n + 26

/-- The scan is linear in volume when a record can hold its address width. -/
theorem elementaryScanCost_le_volume (n M B : ℕ) (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hn : n ≤ B) : elementaryScanCost n M B ≤ 108 * M * B := by
  have h₁ := Nat.mul_le_mul_left M hn
  have h₂ : M ≤ M * B := Nat.le_mul_of_pos_right M hB
  have h₃ : B ≤ M * B := Nat.le_mul_of_pos_left B hM
  unfold elementaryScanCost
  nlinarith

def lowBitXorProgram {T Q A t₀ : ℕ} {U P : Type} (rg : LayReg t₀ → Fin T) :
    Pr P T Q A U :=
  fixAt (rg .str) (rg .r0) (rg .r1) (rg .r2) (rg .r3) (rg .q0) (rg .q1) (rg .q2) (rg .q3)
    (rg .ctrB) (rg .cnt) (rg .tmp) (rg .st) (fun _ : Fin 1 => rg .fld) ![rg .fld, rg .mA, rg .mB]
    (fun r => rg (.us r)) (xorBitCodeAuto A) (layCodeAuto A 1)

/-- The complete elementary pass is an actual program with a restored frame.
The explicit bound is O(record volume plus record count times address width).
Masks and counters are prepared inputs; their generation remains caller work. -/
theorem lowBitXor_exec {T Q A t₀ : ℕ} {U P : Type}
    (body : P → Pr P T Q A U) {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg)
    {n R B s : ℕ} (hn : 0 < n) (hs : 0 < s) (hsn : s < n) (hB : 1 ≤ B)
    (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ n) (hlB : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg .str) = l.flatten)
    (hcfg : ElementaryCfg rg S.R n (R * 2 ^ n) B 0 s) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ elementaryScanCost n (R * 2 ^ n) B ∧
      Exec body (lowBitXorProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (lowBitXorPerm n s R hn hs) l).flatten }) := by
  have hin : idxCode (xorBitCodeAuto A) n (fun _ : Fin 1 => n) (layRsrc 0 s) =
      lowBitXorCode s := funext (xorBitIdxCode A n s hn hsn)
  have houtcode : idxCode (layCodeAuto A 1) n (fun _ : Fin 1 => n) (layRsrc 0 s) =
      lowBitCode := funext (lowBitIdxCode A n s hn)
  obtain ⟨hmerge, hcount⟩ := lowBitXor_merge hn hs l hl hlB
  have hlen : (moveRecs (lowBitXorPerm n s R hn hs) l).flatten.length = R * 2 ^ n * B := by
    rw [length_flatten_of_length _ (fun r hr => hlB r (mem_moveRecs _ hl hr)), length_moveRecs]
  have hI : IdxState (fun _ : Fin 1 => rg .fld) (fun _ => n) n ![rg .fld, rg .mA, rg .mB]
      (fun r => rg (.us r)) (layRsrc 0 s) S.R 0 := by
    refine ⟨fun f => ?_, fun r p hr => ?_, fun r => hcfg.us r⟩
    · rw [hcfg.fld]
      simp [digit]
    · fin_cases r
      · simp [layRsrc] at hr
      · simp only [layRsrc] at hr
        simp at hr
        subst hr
        exact hcfg.mA
      · simp only [layRsrc] at hr
        simp at hr
        subst hr
        exact hcfg.mB
  obtain ⟨v', m, hu, hm, he⟩ := fixAt_exec body (layFixLayout hrg n 0 s)
    (xorBitCodeAuto A) (layCodeAuto A 1) hB l hl hlB
    (by simpa only [hin, houtcode] using hcount) _ hlen
    (by simpa only [hin, houtcode] using hmerge) v S hsrc
    hcfg.r0 hcfg.r1 hcfg.r2 hcfg.r3 hcfg.q0 hcfg.q1 hcfg.q2 hcfg.q3
    hcfg.ctrB hcfg.cnt hcfg.tmp hI
  refine ⟨v', m, hu, hm.trans (le_of_eq ?_), he⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, elementaryScanCost]
  ring

end IntegerMultBounds.MathlibTM2.Routing
