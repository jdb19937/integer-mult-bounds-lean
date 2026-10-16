module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBList
public import IntegerMultBounds.MathlibTM2.Fast.ResampBAxis

/-!
# `B̃₀` along every axis of the padded box: the stream semantics

A box array on `∏_{i<d} ZMod (M i)` is stored on the padded box `∏_{i<d} [0, M i)` as the
stream `rsbBox d M F` of its numerators, axis `0` most significant. `B̃₀` maps arrays on
`∏ ZMod (t i)` to arrays on `∏ ZMod (s i)`, `s i ≤ t i`; its output is stored on the same padded
box `∏ [0, t i)`, with zeros at every address with some coordinate `x i ≥ s i`.

* `RsbLineRel M N A g q`: the list map `g` (lines of `M` records to lines of `M` records)
  computes the numerators at scale `2^q` of the numeric map `A : (ZMod M → ℂ) → ZMod N → ℂ` on
  its first `N` outputs, has zeros in the outputs `N ≤ k`, and maps zero lines to zero lines.
* `rsb_tensor`: line maps `g i` related to `A i` along all axes, in the order of `tensorZR`
  (`rsbAxesL`), turn the stream of the numerators of `u` into the padded stream of the
  numerators of `tensorZR d M N A u`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.NLogN

noncomputable section

/-- The integer line map `g` (lines of `M` records) gives the numerators at scale `2^q` of the
numeric map `A` on its first `N` outputs, zeros on the others, and zeros on zero lines. -/
structure RsbLineRel (M N : ℕ) (A : (ZMod M → ℂ) → ZMod N → ℂ)
    (g : List GaussianInt → List GaussianInt) (q : ℕ) : Prop where
  num : ∀ (L : List GaussianInt) (v : ZMod M → ℂ),
    (∀ j : ZMod M, v j = GaussianInt.toComplex (L.getD j.val 0) / 2 ^ q) →
      ∀ k : ℕ, k < N → A v (k : ZMod N) = GaussianInt.toComplex ((g L).getD k 0) / 2 ^ q
  pad : ∀ (L : List GaussianInt) (k : ℕ), N ≤ k → (g L).getD k 0 = 0
  zero : ∀ L : List GaussianInt, (∀ x ∈ L, x = 0) → ∀ k : ℕ, (g L).getD k 0 = 0

/-- **Line maps along all axes compute `tensorZR` on the padded box.** Let `F` be the stream of
the numerators of `u` at scale `2^q` on the box `∏ [0, M i)`, and let every line map `g i` be
related to `A i` (`RsbLineRel`). Then the line maps along all axes turn `rsbBox d M F` into
`rsbBox d M G`, where `G` holds the numerators of `tensorZR d M N A u` at the addresses below `N`
and zeros elsewhere. -/
theorem rsb_tensor : ∀ (d : ℕ) (M N : Fin d → ℕ) [∀ i, NeZero (M i)] [∀ i, NeZero (N i)]
    (_ : ∀ i, N i ≤ M i) (A : (i : Fin d) → (ZMod (M i) → ℂ) → ZMod (N i) → ℂ)
    (g : Fin d → List GaussianInt → List GaussianInt) (q : ℕ)
    (_ : ∀ i : Fin d, RsbLineRel (M i) (N i) (A i) (g i) q)
    (u : ((i : Fin d) → ZMod (M i)) → ℂ) (F : ((i : Fin d) → Fin (M i)) → GaussianInt)
    (_ : ∀ x : (i : Fin d) → Fin (M i),
      u (fun i => ((x i : ℕ) : ZMod (M i))) = GaussianInt.toComplex (F x) / 2 ^ q),
    ∃ G : ((i : Fin d) → Fin (M i)) → GaussianInt,
      (∀ x : (i : Fin d) → Fin (M i), (∀ i, (x i : ℕ) < N i) →
        tensorZR d M N A u (fun i => ((x i : ℕ) : ZMod (N i))) =
          GaussianInt.toComplex (G x) / 2 ^ q) ∧
      (∀ x : (i : Fin d) → Fin (M i), (∃ i, N i ≤ x i) → G x = 0) ∧
      rsbAxesL d M g (rsbBox d M F) = rsbBox d M G
  | 0, M, N, _, _, _, A, g, q, _, u, F, hF => by
      refine ⟨F, fun x _ => ?_, fun x ⟨i, _⟩ => i.elim0, rfl⟩
      have h := hF x
      have e : (fun i => ((x i : ℕ) : ZMod (M i))) = fun i => i.elim0 := funext fun i => i.elim0
      rw [e] at h
      simpa [tensorZR] using h
  | d + 1, M, N, _, _, hNM, A, g, q, hA, u, F, hF => by
      set Q := ∏ i : Fin d, M i.succ with hQ
      have hA' : ∀ i : Fin d, RsbLineRel (M i.succ) (N i.succ) (A i.succ) (g i.succ) q :=
        fun i => hA i.succ
      have key : ∀ x₀ : Fin (M 0), ∃ G' : ((i : Fin d) → Fin (M i.succ)) → GaussianInt,
          (∀ y : (i : Fin d) → Fin (M i.succ), (∀ i, (y i : ℕ) < N i.succ) →
            tensorZR d (fun i => M i.succ) (fun i => N i.succ) (fun i => A i.succ)
              (fun j' => u (Fin.cons (((x₀ : ℕ) : ZMod (M 0))) j'))
              (fun i => ((y i : ℕ) : ZMod (N i.succ))) = GaussianInt.toComplex (G' y) / 2 ^ q) ∧
          (∀ y : (i : Fin d) → Fin (M i.succ), (∃ i, N i.succ ≤ y i) → G' y = 0) ∧
          rsbAxesL d (fun i => M i.succ) (fun i => g i.succ)
            (rsbBox d (fun i => M i.succ) (fun y => F (Fin.cons x₀ y))) =
            rsbBox d (fun i => M i.succ) G' := by
        intro x₀
        exact rsb_tensor d (fun i => M i.succ) (fun i => N i.succ) (fun i => hNM i.succ)
          (fun i => A i.succ) (fun i => g i.succ) q hA'
          (fun j' => u (Fin.cons (((x₀ : ℕ) : ZMod (M 0))) j')) (fun y => F (Fin.cons x₀ y))
          (fun y => by
            rw [← hF (Fin.cons x₀ y)]
            congr 1
            funext i
            refine Fin.cases ?_ (fun i => ?_) i <;> simp)
      choose Gs hGs using key
      set Gm : ((i : Fin (d + 1)) → Fin (M i)) → GaussianInt := fun x => Gs (x 0) (Fin.tail x)
        with hGm
      have hchunk : rsbChunkMap Q (M 0) (rsbAxesL d (fun i => M i.succ) (fun i => g i.succ))
          (rsbBox (d + 1) M F) = rsbBox (d + 1) M Gm :=
        rsbChunkMap_box d M _ F Gm (fun x₀ => by
          rw [(hGs x₀).2.2]
          simp [hGm])
      refine ⟨fun x => (g 0 ((List.finRange (M 0)).map fun j =>
        Gm (Fin.cons j (Fin.tail x)))).getD (x 0) 0, fun x hx => ?_, fun x hx => ?_, ?_⟩
      · -- the numerators
        set L := (List.finRange (M 0)).map fun j => Gm (Fin.cons j (Fin.tail x)) with hL
        have hv : ∀ j₀ : ZMod (M 0),
            tensorZR d (fun i => M i.succ) (fun i => N i.succ) (fun i => A i.succ)
              (fun j' => u (Fin.cons j₀ j')) (fun i => ((x i.succ : ℕ) : ZMod (N i.succ))) =
            GaussianInt.toComplex (L.getD j₀.val 0) / 2 ^ q := by
          intro j₀
          have hj : j₀.val < M 0 := ZMod.val_lt j₀
          have h1 := (hGs ⟨j₀.val, hj⟩).1 (Fin.tail x) (fun i => hx i.succ)
          simp only [ZMod.natCast_val, ZMod.cast_id', id] at h1
          rw [show (fun i : Fin d => ((x i.succ : ℕ) : ZMod (N i.succ))) =
            fun i => (((Fin.tail x) i : ℕ) : ZMod (N i.succ)) from rfl, h1]
          congr 2
          rw [hL, List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map,
            List.getElem_finRange]
          simp [hGm]
        have h := (hA 0).num L _ hv (x 0) (hx 0)
        have hT : tensorZR (d + 1) M N A u (fun i => ((x i : ℕ) : ZMod (N i))) =
            A 0 (fun j₀ : ZMod (M 0) => tensorZR d (fun i => M i.succ) (fun i => N i.succ)
              (fun i => A i.succ) (fun j' => u (Fin.cons j₀ j'))
              (fun i => ((x i.succ : ℕ) : ZMod (N i.succ)))) ((x 0 : ℕ) : ZMod (N 0)) := rfl
        rw [hT, h]
      · -- the padding
        obtain ⟨i, hi⟩ := hx
        refine Fin.cases (motive := fun i => N i ≤ x i → _) (fun h0 => ?_) (fun i' hi' => ?_) i hi
        · exact (hA 0).pad _ _ h0
        · apply (hA 0).zero
          intro z hz
          simp only [List.mem_map, List.mem_finRange, true_and] at hz
          obtain ⟨j, rfl⟩ := hz
          simp only [hGm, Fin.cons_zero, Fin.tail_cons]
          exact (hGs j).2.1 (Fin.tail x) ⟨i', hi'⟩
      · show rsbAxisL 1 (M 0) Q (g 0) (rsbChunkMap Q (M 0)
          (rsbAxesL d (fun i => M i.succ) (fun i => g i.succ)) (rsbBox (d + 1) M F)) = _
        rw [hchunk, rsbAxisL_box]

/-! ### The line map of the machine -/

section LineRel

variable {s t : ℕ}

lemma tdivN_zero (p : ℕ) : tdivN p 0 = 0 := by ext <;> simp [tdivN]

end LineRel

end

end IntegerMultBounds.MathlibTM2.Fast
