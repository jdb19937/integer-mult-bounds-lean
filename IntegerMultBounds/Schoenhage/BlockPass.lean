module

public import IntegerMultBounds.Schoenhage.PrefixRoundWords

/-! One prefix-round pass on word tapes, over any tapes of a bank: the zipped
sums and complement sums of two word lists (`runs_zipAddSub`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Rules

variable {a t : ℕ}

/-- The sum of one pair of words to `S1` and its complement sum to `S2`. -/
noncomputable def zipBody (X Y S1 S2 : Fin t) (h1 : X ≠ Y) (h2 : X ≠ S1) (h3 : Y ≠ S1) (h4 : X ≠ S2)
    (h5 : Y ≠ S2) : Cmd a t :=
  .seq (op1 Rules.add false X Y S1 h1 h2 h3) <| .seq (back X) <| .seq (back Y)
    (op1 Rules.addNot false X Y S2 h1 h4 h5)

/-- Zip the word lists of `X` and `Y`. -/
noncomputable def zipAddSub (X Y S1 S2 : Fin t) (h1 : X ≠ Y) (h2 : X ≠ S1) (h3 : Y ≠ S1) (h4 : X ≠ S2)
    (h5 : Y ≠ S2) : Cmd a t :=
  .loop X (zipBody X Y S1 S2 h1 h2 h3 h4 h5)

theorem runs_zipBody {X Y S1 S2 : Fin t} (h1 : X ≠ Y) (h2 : X ≠ S1) (h3 : Y ≠ S1) (h4 : X ≠ S2)
    (h5 : Y ≠ S2) (h6 : S1 ≠ S2) (σ : Fin t → WTape) {LX LY M1 M2 xs ys : List (List Bool)} {x y : List Bool}
    (hX : σ X = ⟨LX, x :: xs⟩) (hY : σ Y = ⟨LY, y :: ys⟩) (hS1 : σ S1 = ⟨M1, []⟩) (hS2 : σ S2 = ⟨M2, []⟩)
    (hxy : x.length = y.length) :
    Runs (a := a) (zipBody X Y S1 S2 h1 h2 h3 h4 h5) σ
      (· = Function.update (Function.update (Function.update (Function.update σ X ⟨x :: LX, xs⟩)
        Y ⟨y :: LY, ys⟩) S1 ⟨addW false x y :: M1, []⟩) S2 ⟨addW true x (cmpl y) :: M2, []⟩)
      (6 * x.length + 40) := by
  apply Runs.of_wp
  simp only [zipBody, WP, wp_op1, wp_back]
  have t1 := time_le Rules.add x (fun _ => y) y.length (fun _ => le_rfl)
  have t2 := time_le Rules.addNot x (fun _ => y) y.length (fun _ => le_rfl)
  simp [hX, hY, hS1, hS2, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm,
    Function.update_apply, WTape.next, WTape.cur, WTape.put, Rules.output_add,
    Rules.output_addNot x (fun _ => y) (by simp [hxy])]
  refine ⟨?_, ?_⟩
  · funext z
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> simp_all
  · have hb1 : Rules.add.B = 2 := rfl
    have hb2 : Rules.addNot.B = 2 := rfl
    rw [hb1] at t1; rw [hb2] at t2
    omega

theorem runs_zipAddSub {X Y S1 S2 : Fin t} (h1 : X ≠ Y) (h2 : X ≠ S1) (h3 : Y ≠ S1) (h4 : X ≠ S2)
    (h5 : Y ≠ S2) (h6 : S1 ≠ S2) (W : ℕ) :
    ∀ (xs ys : List (List Bool)) (σ : Fin t → WTape) (LX LY M1 M2 : List (List Bool)),
      σ X = ⟨LX, xs⟩ → σ Y = ⟨LY, ys⟩ → σ S1 = ⟨M1, []⟩ → σ S2 = ⟨M2, []⟩ →
      xs.length = ys.length → (∀ i < xs.length, (xs.getD i []).length = W ∧ (ys.getD i []).length = W) →
      Runs (a := a) (zipAddSub X Y S1 S2 h1 h2 h3 h4 h5) σ
        (· = Function.update (Function.update (Function.update (Function.update σ X ⟨xs.reverse ++ LX, []⟩)
          Y ⟨ys.reverse ++ LY, []⟩) S1 ⟨(List.zipWith (addW false) xs ys).reverse ++ M1, []⟩)
          S2 ⟨(List.zipWith (fun x y => addW true x (cmpl y)) xs ys).reverse ++ M2, []⟩)
        (xs.length * (6 * W + 42))
  | [], ys, σ, LX, LY, M1, M2, hX, hY, hS1, hS2, hl, _ => by
    have hys : ys = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst hys
    refine (Runs.loop_done (by simp [hX]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext z
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> simp_all
  | x :: xs, ys, σ, LX, LY, M1, M2, hX, hY, hS1, hS2, hl, hW => by
    obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
      cases ys with
      | nil => simp at hl
      | cons y ys' => exact ⟨y, ys', rfl⟩
    have hx := (hW 0 (by simp)).1
    have hy := (hW 0 (by simp)).2
    simp only [List.getD_cons_zero] at hx hy
    have s1 := runs_zipBody (a := a) h1 h2 h3 h4 h5 h6 σ hX hY hS1 hS2 (by rw [hx, hy])
    set σ₁ := Function.update (Function.update (Function.update (Function.update σ X ⟨x :: LX, xs⟩)
        Y ⟨y :: LY, ys'⟩) S1 ⟨addW false x y :: M1, []⟩) S2 ⟨addW true x (cmpl y) :: M2, []⟩
    have ih := runs_zipAddSub h1 h2 h3 h4 h5 h6 W xs ys' σ₁ (x :: LX) (y :: LY) (addW false x y :: M1)
      (addW true x (cmpl y) :: M2)
      (by simp [σ₁, h1, h2, h4]) (by simp [σ₁, h3, h5])
      (by simp [σ₁, h6]) (by simp [σ₁])
      (by simpa using hl) (fun i hi => by have := hW (i + 1) (by simp; omega); simpa using this)
    refine (Runs.loop_step (by simp [hX]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
      (fun σ' h' => ?_) ?_
    · rw [h']
      funext z
      simp only [Function.update_apply, σ₁]
      split_ifs <;> (try subst_vars) <;> simp_all
    · simp only [List.length_cons, hx]; nlinarith

end IntegerMultBounds.Schoenhage
