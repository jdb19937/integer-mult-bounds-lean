module

public import IntegerMultBounds.MathlibTM2.Routing.SelfRead

/-!
# Active packed targets

A false mask entry suppresses the control of that digit. The visible observation
retains the complete digit at inactive positions and only the upper part at
active ones. Thus inactive digit low bits can be sources of other updates.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-- Suppress controls outside the active target set. -/
def maskBits (active : List Bool) (zs : List ℤ) : List ℤ :=
  List.zipWith (fun a z => if a then z else 0) active zs

/-- Exactly the target data which a selective update must preserve. -/
def visible (active : List Bool) (vs : List ℤ) : List ℤ :=
  List.zipWith (fun a v => if a then v / 2 else v) active vs

theorem maskBits_length (active : List Bool) (zs : List ℤ)
    (hlen : active.length = zs.length) : (maskBits active zs).length = active.length := by
  simp [maskBits, hlen]

theorem maskBits_bits (active : List Bool) (zs : List ℤ) (hz : Bits zs) :
    Bits (maskBits active zs) := by
  induction active generalizing zs with
  | nil => simp [maskBits, Bits]
  | cons a active ih =>
    cases zs with
    | nil => simp [maskBits, Bits]
    | cons z zs =>
      have hz₀ := hz z (by simp)
      have hzs : Bits zs := fun z hz' => hz z (by simp [hz'])
      intro v hv
      simp only [maskBits, List.zipWith_cons_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · cases a <;> simp_all
      · exact ih zs hzs v hv

/-- Active upper parts and whole inactive digits survive an early pass. -/
theorem visible_toggle (active : List Bool) (vs zs : List ℤ)
    (hv : active.length = vs.length) (hzlen : active.length = zs.length) (hz : Bits zs) :
    visible active (toggleList vs (maskBits active zs)) = visible active vs := by
  induction active generalizing vs zs with
  | nil => simp [visible]
  | cons a active ih =>
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      cases zs with
      | nil => simp at hzlen
      | cons z zs =>
        have hz₀ := hz z (by simp)
        have hzs : Bits zs := fun z hz' => hz z (by simp [hz'])
        have ht := ih vs zs (by simpa using hv) (by simpa using hzlen) hzs
        change (if a then toggle v (if a then z else 0) / 2
          else toggle v (if a then z else 0)) ::
            visible active (toggleList vs (maskBits active zs)) =
              (if a then v / 2 else v) :: visible active vs
        rw [ht]
        congr 1
        cases a
        · simp [toggle]
        · simpa using toggle_guard v z hz₀

/-- Dirty controls cancel at active targets and have no effect at inactive ones. -/
theorem masked_later_source (active : List Bool) (vs us zs : List ℤ)
    (hv : active.length = vs.length) (hu : active.length = us.length)
    (hzlen : active.length = zs.length) (hz : Bits zs) :
    toggleList (toggleList vs (maskBits active (us.map (· % 2))))
      (maskBits active ((List.zipWith (· + ·) us zs).map (· % 2))) =
        toggleList vs (maskBits active zs) := by
  induction active generalizing vs us zs with
  | nil => simp [maskBits, toggleList]
  | cons a active ih =>
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      cases us with
      | nil => simp at hu
      | cons u us =>
        cases zs with
        | nil => simp at hzlen
        | cons z zs =>
          have hz₀ := hz z (by simp)
          have hzs : Bits zs := fun z hz' => hz z (by simp [hz'])
          have ht := ih vs us zs (by simpa using hv) (by simpa using hu)
            (by simpa using hzlen) hzs
          change toggle (toggle v (if a then u % 2 else 0))
            (if a then (u + z) % 2 else 0) :: _ =
              toggle v (if a then z else 0) :: _
          congr 1
          · cases a
            · simp [toggle]
            · exact later_source v u z hz₀

/-- A masked complete early pass, with actual dirty control digits. -/
def maskedEarly (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) : Equiv.Perm (LateAddress B L n) :=
  fiberPerm fun u => packedEarlyPermN (2 * L) B (by omega) (by omega) n
    (maskBits active ((digits B n u.val).map (· % 2)))

/-- The physical source observation after a masked complete early pass. -/
def sourceView (B L : ℤ) {n : ℕ} (active : List Bool) (x : EarlyAddress B L n) : List ℤ :=
  visible active (digits (2 * L) n x.1.val)

private theorem early_endpoint (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    {n : ℕ} (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs)
    (x : EarlyAddress B L n) (hx : earlyGood B L n x) :
    let y := packedEarlyPermN (2 * L) B (by omega) (by omega) n zs x
    y.2 = x.2 ∧ digits (2 * L) n y.1.val = toggleList (digits (2 * L) n x.1.val) zs ∧
      earlyGood B L n y := by
  subst n
  dsimp only
  have heq : packedEarlyPermN (2 * L) B (by omega) (by omega) zs.length zs x =
      earlyIdeal B L hL zs hz x := early_program_agrees_on_good B L hB hL zs hz x hx
  rw [heq]
  exact ⟨rfl, idealTarget_digits L hL zs hz x.1,
    (earlyIdeal_preserves_good B L hL zs hz x).mpr hx⟩

/-- Inactive low bits are preserved as well as all upper target bits. -/
theorem maskedEarly_endpoint (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    {n : ℕ} (active : List Bool) (hlen : active.length = n)
    (x : LateAddress B L n) (hx : earlyGood B L n x.2) :
    let y := maskedEarly B L hB hL active x
    y.1 = x.1 ∧ y.2.2 = x.2.2 ∧ earlyGood B L n y.2 ∧
      sourceView B L active y.2 = sourceView B L active x.2 := by
  have hpar : Bits ((digits B n x.1.val).map (· % 2)) := by
    intro z hz
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    omega
  have hlength : active.length = ((digits B n x.1.val).map (· % 2)).length := by
    simp [digits_length, hlen]
  obtain ⟨hw, hd, hg⟩ := early_endpoint B L hB hL _
    ((maskBits_length active _ hlength).trans hlen) (maskBits_bits active _ hpar) x.2 hx
  refine ⟨rfl, hw, hg, ?_⟩
  dsimp only [maskedEarly, fiberPerm, Equiv.coe_fn_mk, sourceView]
  rw [hd]
  exact visible_toggle active _ _ (by simp [digits_length, hlen]) hlength hpar

private theorem add_bits_bounded (B : ℤ) (us zs : List ℤ)
    (hu : ∀ u ∈ us, 0 ≤ u ∧ u < B - 1) (hz : Bits zs) :
    Bounded B (List.zipWith (· + ·) us zs) := by
  induction us generalizing zs with
  | nil => simp [Bounded]
  | cons u us ih =>
    cases zs with
    | nil => simp [Bounded]
    | cons z zs =>
      rw [List.zipWith_cons_cons, bounded_cons]
      have hu₀ := hu u (by simp)
      have hz₀ := hz z (by simp)
      refine ⟨by rcases hz₀ with rfl | rfl <;> omega, ?_⟩
      exact ih zs (fun u h => hu u (by simp [h])) (fun z h => hz z (by simp [h]))

/-- The good-set load has no carry between compact control digits. -/
theorem control_load_digits (B : ℤ) (hB : 0 < B) {n : ℕ} (u : Field (B ^ n))
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs)
    (hu : ∀ z ∈ digits B n u.val, z < B - 1) :
    digits B n (fieldAdd (pow_pos hB n) u (pack B zs)).val =
      List.zipWith (· + ·) (digits B n u.val) zs := by
  have hlen' : (digits B n u.val).length = zs.length := by rw [digits_length, hlen]
  have hbounded : Bounded B (List.zipWith (· + ·) (digits B n u.val) zs) :=
    add_bits_bounded B _ _ (fun z hz' =>
      ⟨(digits_bounded B hB n u.val z hz').1, hu z hz'⟩) hz
  have hp := pack_bounds B hB _ hbounded
  have hl : (List.zipWith (· + ·) (digits B n u.val) zs).length = n := by
    simp [digits_length, hlen]
  have he : u.val + pack B zs = pack B (List.zipWith (· + ·) (digits B n u.val) zs) := by
    rw [pack_add B _ _ hlen', pack_digits B hB n u.val u.property]
  change digits B n ((u.val + pack B zs) % B ^ n) = _
  have hp' : pack B (List.zipWith (· + ·) (digits B n u.val) zs) < B ^ n := by
    simpa only [hl] using hp.2
  rw [he, Int.emod_eq_of_lt hp.1 hp']
  simpa only [hl] using digits_pack B hB _ hbounded

private theorem parity_bits (vs : List ℤ) : Bits (vs.map (· % 2)) := by
  intro z hz
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
  omega

private theorem maskedEarly_digits (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    {n : ℕ} (active : List Bool) (hlen : active.length = n)
    (x : LateAddress B L n) (hx : earlyGood B L n x.2) :
    digits (2 * L) n (maskedEarly B L hB hL active x).2.1.val =
      toggleList (digits (2 * L) n x.2.1.val)
        (maskBits active ((digits B n x.1.val).map (· % 2))) := by
  have hlength : active.length = ((digits B n x.1.val).map (· % 2)).length := by
    simp [digits_length, hlen]
  exact (early_endpoint B L hB hL _ ((maskBits_length active _ hlength).trans hlen)
    (maskBits_bits active _ (parity_bits _)) x.2 hx).2.1

theorem ideal_digits (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs) (x : LateAddress B L n) :
    digits (2 * L) n (ideal B L hL zs hlen hz x).2.1.val =
      toggleList (digits (2 * L) n x.2.1.val) zs := by
  subst n
  exact idealTarget_digits L hL zs hz x.2.1

/-- The fixed-source masked program: two early passes and the real modular load/unload. -/
def maskedFrozen (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (zs : List ℤ) : Equiv.Perm (LateAddress B L n) :=
  let E := maskedEarly B L hB hL (n := n) active
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun _ : EarlyAddress B L n => pack B zs)
  E.trans (load.trans (E.trans load.symm))

/-- Two masked passes cancel arbitrary dirty controls and toggle only active targets. -/
theorem maskedFrozen_good (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (zs : List ℤ) (hlen : zs.length = n)
    (hz : Bits zs) (x : LateAddress B L n) (hx : lateGood B L n x) :
    maskedFrozen B L hB hL active zs x =
      ideal B L hL (maskBits active zs)
        ((maskBits_length active zs (ha.trans hlen.symm)).trans ha)
        (maskBits_bits active zs hz) x := by
  let E := maskedEarly B L hB hL (n := n) active
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun _ : EarlyAddress B L n => pack B zs)
  let a := E x
  let b := load a
  let c := E b
  obtain ⟨haU, haW, haGood, _⟩ := maskedEarly_endpoint B L hB hL active ha x hx.1
  obtain ⟨hcU, hcW, _, _⟩ := maskedEarly_endpoint B L hB hL active ha b haGood
  have haD := maskedEarly_digits B L hB hL active ha x hx.1
  have hcD := maskedEarly_digits B L hB hL active ha b haGood
  have hbU : b.1 = fieldAdd (pow_pos (show 0 < B by omega) n) x.1 (pack B zs) := by
    change fieldAdd (pow_pos (show 0 < B by omega) n) (E x).1 (pack B zs) = _
    rw [haU]
  have hbD := control_load_digits B (by omega) x.1 zs hlen hz hx.2
  have hd : digits (2 * L) n c.2.1.val =
      toggleList (digits (2 * L) n x.2.1.val) (maskBits active zs) := by
    change digits (2 * L) n (E b).2.1.val = _
    rw [hcD]
    change toggleList (digits (2 * L) n a.2.1.val)
      (maskBits active ((digits B n b.1.val).map (· % 2))) = _
    rw [haD, hbU, hbD]
    exact masked_later_source active _ _ zs (by simp [digits_length, ha])
      (by simp [digits_length, ha]) (ha.trans hlen.symm) hz
  have hu : (load.symm c).1 = x.1 := by
    change fieldAdd (pow_pos (show 0 < B by omega) n) (E b).1 (-pack B zs) = _
    rw [hcU, hbU]
    exact fieldAdd_cancel _ x.1 (pack B zs)
  have hw : (load.symm c).2.2 = x.2.2 := hcW.trans haW
  have hiD : digits (2 * L) n
      (ideal B L hL (maskBits active zs)
        ((maskBits_length active zs (ha.trans hlen.symm)).trans ha)
        (maskBits_bits active zs hz) x).2.1.val =
          toggleList (digits (2 * L) n x.2.1.val) (maskBits active zs) := by
    exact ideal_digits B L hL _ _ _ x
  have he := ideal_endpoint B L hL (maskBits active zs)
    ((maskBits_length active zs (ha.trans hlen.symm)).trans ha) (maskBits_bits active zs hz) x
  apply Prod.ext
  · exact hu.trans he.1.symm
  apply Prod.ext
  · apply Subtype.ext
    have hp := congrArg (pack (2 * L)) (hd.trans hiD.symm)
    have hp' := hp
    rw [pack_digits (2 * L) (by omega) n _ c.2.1.property,
      pack_digits (2 * L) (by omega) n _
        (ideal B L hL (maskBits active zs) _ _ x).2.1.property] at hp'
    simpa only [c, b, a, E, load, maskedFrozen, Equiv.trans_apply, rotateLeft, Equiv.symm,
      Equiv.coe_fn_mk] using hp'
  · exact hw.trans he.2.1.symm

end IntegerMultBounds.MathlibTM2.Routing.Packed
