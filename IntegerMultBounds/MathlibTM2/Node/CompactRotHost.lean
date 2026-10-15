module

public import IntegerMultBounds.MathlibTM2.Host.PlacedSwap

/-! # Normalized host transport for compact native banks

This reusable transport includes header shifts, normalization and an arbitrary
unplaced frame. Concrete compact stage contracts instantiate it separately.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
noncomputable section
variable {N H T Q A : ℕ} {U F : Type}

abbrev compactNativePlacement (ι : Fin N → Fin T) (hι : Function.Injective ι) (hT : N ≤ T) :
    Fin (N + (T-N)) ≃ Fin T :=
  InjectivePlacement.placement ι hι (Nat.add_sub_cancel' hT)

def compactNativeProg (M : Program N Q A) (hdr : Fin H → Fin N)
    (ι : Fin N → Fin T) (hι : Function.Injective ι) (hT : N ≤ T) : Pr F T Q A U :=
  .seq (markList (unplaced ι))
    (.seq (shiftList (List.ofFn (ι ∘ hdr)))
      (.seq (foreign (Placement.placed M (compactNativePlacement ι hι hT)))
        (.seq (normList (List.ofFn ι)) (dropList (unplaced ι)))))

/-- A proved native contract transports to actual normalized host stacks.
The finite bank and all header shifts are explicit in the program. -/
theorem compactNativeProg_exec (body : F → Pr F T Q A U)
    (M : Program N Q A) (hdr : Fin H → Fin N) (hh : Function.Injective hdr)
    (ι : Fin N → Fin T) (hι : Function.Injective ι) (hT : N ≤ T)
    (B B' : Tapes N A) (cost : ℕ)
    (hM : HoareTime M (fun w => w=B) (fun w => w=B') cost)
    (words words' : Fin N → List (Fin (A+4)))
    (hhead : ∀ j, B.head j = if j ∈ Set.range hdr then 1 else 0)
    (htape : ∀ j, B.tape j = wordTape (words j))
    (htape' : ∀ j, B'.tape j = wordTape (words' j))
    (hhword : ∀ k, words (hdr k) ≠ [])
    (hfree : ∀ j, blank ∉ words' j)
    (v : HS T Q A U) (S : Stacks T A)
    (hL : ∀ j, S.L (ι j)=[]) (hR : ∀ j, S.R (ι j)=words j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*N+5)*cost + 6*(∑ j, (words j).length) + 2*T+6*N+H+10 ∧
      Exec body (compactNativeProg M hdr ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun y => if y ∈ Set.range ι then [] else S.L y
          R := fun y => if h : y ∈ Set.range ι then words' (Classical.choose h) else S.R y }) := by
  let pe := compactNativePlacement ι hι hT
  have hun : ∀ j, ι j ∉ unplaced ι := fun j hm => (mem_unplaced ι _).1 hm j rfl
  have he₀ := markList_exec body (unplaced ι) (unplaced_nodup ι) v S
  let S₀ : Stacks T A := { S with R := fun y => if y ∈ unplaced ι then blank :: S.R y else S.R y }
  let hs := List.ofFn (ι ∘ hdr)
  have hnd : hs.Nodup := List.nodup_ofFn.2 (hι.comp hh)
  have hmem : ∀ y, y ∈ hs ↔ ∃ k, ι (hdr k)=y := fun y => List.mem_ofFn
  obtain ⟨v₁, hu₁, he₁⟩ := shiftList_exec body hs hnd v S₀
  let S₁ : Stacks T A := { S₀ with
    L := fun y => if y ∈ hs then (S₀.R y).head?.getD blank :: S₀.L y else S₀.L y
    R := fun y => if y ∈ hs then (S₀.R y).tail else S₀.R y }
  have hhdr : ∀ k, S₁.L (ι (hdr k)) = [(words (hdr k)).head?.getD blank] ∧
      S₁.R (ι (hdr k)) = (words (hdr k)).tail := by
    intro k
    have hm : ι (hdr k) ∈ hs := (hmem _).2 ⟨k,rfl⟩
    simp [S₁, S₀, hm, hun, hL, hR]
  have hother : ∀ j, j ∉ Set.range hdr → S₁.L (ι j)=[] ∧ S₁.R (ι j)=words j := by
    intro j hj
    have hm : ι j ∉ hs := by
      intro hm; obtain ⟨k,hk⟩ := (hmem _).1 hm
      exact hj ⟨k,hι hk⟩
    simp [S₁,S₀,hm,hun,hL,hR]
  have houtside : ∀ y, (∀ j, ι j ≠ y) → S₁.L y=S.L y ∧ S₁.R y=blank::S.R y := by
    intro y hy
    have hm : y ∉ hs := by intro hm; obtain ⟨k,hk⟩ := (hmem _).1 hm; exact hy _ hk
    have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy
    simp [S₁,S₀,hm,hu]
  have hlen : ∀ j, (S₁.L (ι j)).length + (S₁.R (ι j)).length = (words j).length := by
    intro j
    by_cases hj : j ∈ Set.range hdr
    · obtain ⟨k,rfl⟩ := hj
      rw [(hhdr k).1,(hhdr k).2]
      have := hhword k
      cases hw : words (hdr k) with
      | nil => exact False.elim (this hw)
      | cons a as => simp [Nat.add_comm]
    · rw [(hother j hj).1,(hother j hj).2]; simp
  let frame : Tapes T A := ⟨fun _ => 0, fun y z => readAt blank (S₁.L y) (S₁.R y) z⟩
  let W := Placement.replace pe frame B
  have hrep : RepT W S₁.L S₁.R := by
    intro y z
    by_cases hy : ∃ j, ι j=y
    · obtain ⟨j,rfl⟩ := hy
      rw [InjectivePlacement.replace_tape_slot,InjectivePlacement.replace_head_slot]
      rw [htape,hhead]
      by_cases hj : j ∈ Set.range hdr
      · obtain ⟨k,rfl⟩ := hj
        rw [ite_eq_left (Set.mem_range_self k),(hhdr k).1,(hhdr k).2,readAt_single]
        have hw := hhword k
        cases hword : words (hdr k) <;> simp_all
      · rw [ite_eq_right hj,(hother j hj).1,(hother j hj).2,sub_zero,readAt_nil_left]
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j,hj⟩
      rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hy',
        InjectivePlacement.replace_head_other _ _ _ _ _ _ hy']
      change _ = readAt blank (S₁.L y) (S₁.R y) (z-0)
      rw [sub_zero]
  have hpre := Placement.hoare_at hM pe W (Placement.active_replace pe frame B)
  obtain ⟨v₂,S₂,W',⟨w',hw',hW'⟩,hrep',hu₂,hinp,hout,hlen₂,hfr,m₂,hm₂,he₂⟩ :=
    foreign_exec_frame body _ (placed_idle_injective _ ι hι _) hpre v₁ S₁ W rfl hrep
  subst w'
  have hsweep : ∀ j, sweep (S₂.L (ι j)) (S₂.R (ι j))=words' j := by
    intro j
    refine filter_window (S₂.L (ι j)) (S₂.R (ι j)) (W'.head (ι j)) _ (hfree j) (fun z => ?_)
    have h := hrep' (ι j) z
    rw [hW',InjectivePlacement.replace_tape_slot,htape'] at h
    rw [hW']
    exact h
  have hun₂ : ∀ y, (∀ j, ι j ≠ y) → S₂.L y=S.L y ∧ S₂.R y=blank::S.R y := by
    intro y hy
    have h₁ := houtside y hy
    have h₂ := idle_stacks_eq (hfr y hy) (by rw [h₁.2]; exact List.cons_ne_nil _ _)
    exact ⟨h₂.1.trans h₁.1,h₂.2.trans h₁.2⟩
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := normList_exec body (List.ofFn ι) (List.nodup_ofFn.2 hι) v₂ S₂
  have he₄ := dropList_exec body (unplaced ι) (unplaced_nodup ι) v₃ { S₂ with
    L := fun y => if y ∈ List.ofFn ι then [] else S₂.L y
    R := fun y => if y ∈ List.ofFn ι then sweep (S₂.L y) (S₂.R y) else S₂.R y }
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))) rfl ?_⟩
  · rw [List.map_ofFn,List.sum_ofFn] at hn₃
    have hsum : ∑ j, ((fun y => 6*((S₂.L y).length+(S₂.R y).length)+6) ∘ ι) j ≤
        ∑ j, (6*(words j).length+(12*cost+6)) := by
      apply Finset.sum_le_sum
      intro j _
      have h := hlen₂ (ι j)
      rw [hlen] at h
      simp only [Function.comp_apply]
      omega
    have heq : (∑ j : Fin N, (6*(words j).length+(12*cost+6))) =
        6*(∑ j, (words j).length)+N*(12*cost+6) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,smul_eq_mul]
    have hprod : cost*(T+5)+N*(12*cost+6)=(T+12*N+5)*cost+6*N := by ring
    have hh : hs.length=H := List.length_ofFn
    have hu := unplaced_length_le ι
    rw [hh]
    omega
  · congr 1
    refine Stacks.ext hinp hout ?_ ?_
    · funext y
      by_cases hy : y ∈ Set.range ι
      · have hm : y ∈ List.ofFn ι := List.mem_ofFn.2 hy
        simp [hy,hm]
      · have hm : y ∉ List.ofFn ι := fun hm => hy (List.mem_ofFn.1 hm)
        have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j,hj⟩
        simp [hy,hm,(hun₂ y hy').1]
    · funext y
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨j,hj⟩ := hy
        subst y
        have hm : ι j ∈ List.ofFn ι := List.mem_ofFn.2 ⟨j,rfl⟩
        have hh : ι j ∈ Set.range ι := ⟨j,rfl⟩
        have hc : Classical.choose hh=j := hι (Classical.choose_spec hh)
        simp [hm,hh,hun,hsweep,hc]
      · have hm : y ∉ List.ofFn ι := fun hm => hy (List.mem_ofFn.1 hm)
        have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j,hj⟩
        have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy'
        simp [hy,hm,hu,(hun₂ y hy').2]
end
end IntegerMultBounds.MathlibTM2.Node
