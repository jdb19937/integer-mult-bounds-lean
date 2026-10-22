module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveRepairSpec

/-!
# Executed exact repair of the selective schedule

Instantiate the existing concrete scan/sort/merge/strip machine with the physical
bad code. The partition equalities are proved from the actual and ideal selective
permutations; its exceptional-sort cost uses the exact physical bad-rank count.
A concrete classifier, key pass, register placement and metadata installation
must still instantiate this prepared boundary before R2 is complete.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A nf : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (hs : ∀ c, (s c).Allowed active) (R : ℕ)

open Classical in
/-- The actual repair pass returns the exact ideal stream, including every bad
address. Every working register is restored and all scan/sort/merge costs count. -/
theorem selectiveRepair_exec (body : P → Pr P T Q A U)
    {cp : Pr P T Q A U} {cf : Fin nf → Fin T} {len : Fin nf → ℕ} {st : Fin T}
    {Y : Fin T → Prop} {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop}
    {sel : ℕ → Fin 2} {c : ℕ}
    (cs : CodeSpec body cp cf len st Y Inv sel (selectiveBadCode p X) c)
    {src gR bR g b ctrKB ctrB ctrK cnt tmp : Fin T} {us : Fin 4 → Fin T}
    (hY : ∀ x ∈ [src, gR, bR, g, b, ctrKB, cnt, tmp], ¬ Y x)
    (hcfB : ∀ f, cf f ≠ ctrB) (hcfK : ∀ f, cf f ≠ ctrK)
    (hregs : [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp].Nodup)
    (hus : ∀ r, us r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp])
    (husi : Function.Injective us) (husf : ∀ r f, us r ≠ cf f)
    {k B : ℕ} (hB : 1 ≤ B) (hk : R * 2 ^ fieldsLen (selectiveLen p X) ≤ 2 ^ k)
    (l : List (List (Fin (A + 4))))
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (moveRecs
      (listPerm (selectivePerm p X hG hK hGK active s R) progW)
      (keyRecs k (selectiveIdealPerm hK active s R hs) l)).flatten)
    (hgR : S.R gR = []) (hbR : S.R bR = []) (hg : S.R g = []) (hb : S.R b = [])
    (hctr : (S.R ctrKB).length = k + B) (hctrB : (S.R ctrB).length = B)
    (hctrK : (S.R ctrK).length = k)
    (hcnt : (S.R cnt).length = R * 2 ^ fieldsLen (selectiveLen p X))
    (htmp : S.R tmp = []) (hus0 : ∀ r, S.R (us r) = []) (hI : Inv S.R 0) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (R * 2 ^ fieldsLen (selectiveLen p X)) *
          (2 * idxStepCost c (k + B) len + 6 * (k + B) + 15) +
        k * (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
          fun i => ¬ Good p (selectiveView p X i)).card * (12 * k + 6 * B + 13)) +
        10 * k + 8 * (∑ f, len f) + 8 * nf + 18 ∧
      Exec body (repairAtC cp sel src gR bR g b ctrKB ctrB ctrK cnt tmp st cf us)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R src (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  let actual := listPerm (selectivePerm p X hG hK hGK active s R) progW
  let ideal := selectiveIdealPerm hK active s R hs
  let keyed := keyRecs k ideal l
  have hkeylen : keyed.length = R * 2 ^ fieldsLen (selectiveLen p X) := length_keyRecs _ _ _
  have hkey : ∀ r ∈ keyed, r.length = k + B := keyRecs_length_mem k B ideal l hl hlen
  obtain ⟨hgood, hbad⟩ := selectiveRepair_partition p X hG hK hGK active s hs R k hk l
  obtain ⟨v', steps, hu, hm, he⟩ := repairAtC_exec cs hY hcfB hcfK hregs hus husi husf hB
    (moveRecs actual keyed) (moveRecs ideal keyed) (by simp [length_moveRecs])
    (moveRecs_length_mem actual keyed hkeylen hkey)
    (moveRecs_length_mem ideal keyed hkeylen hkey) hgood hbad v S hsrc hgR hbR hg hb
    hctr hctrB hctrK (by simpa [length_moveRecs] using hcnt) htmp hus0 hI
  rw [map_drop_moveRecs_keyRecs] at he
  rw [selectiveBad_records p X R _ (length_moveRecs _ _), length_moveRecs] at hm
  exact ⟨v', steps, hu, hm, he⟩

open Classical in
/-- The only exceptional-sort term is controlled by the density of the exact
physical bad set; there is no extra extraction-volume assumption. -/
theorem selectiveRepair_sortCost_density (k B : ℕ) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)) :
    ((k * (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card * (12 * k + 6 * B + 13)) : ℕ) : ℝ) ≤
      (k : ℝ) * (5 / (128 * scale ^ 3) *
        (R * 2 ^ fieldsLen (selectiveLen p X) : ℕ) * (12 * k + 6 * B + 13)) := by
  have hd := selectiveBad_repair_density p X R hguard scale hscale hn hradix hgap
  push_cast at hd ⊢
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      hd (by positivity)) (by positivity)

end IntegerMultBounds.MathlibTM2.Routing
