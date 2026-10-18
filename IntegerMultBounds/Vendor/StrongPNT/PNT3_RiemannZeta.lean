module

public import IntegerMultBounds.Vendor.StrongPNT.PNT2_LogDerivative

@[expose] public section

namespace Erdos970


open scoped BigOperators Topology
abbrev ℙ := Nat.Primes

lemma p_s_abs_1 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) < 1 := by
                        
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
                                                                  
  have hnorm_eq : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ = ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s : ℂ))
                                                
  have hz : ((-s : ℂ).re) < 0 := by
    have h0 : 0 < s.re := lt_trans zero_lt_one hs
    have : -s.re < 0 := neg_lt_zero.mpr h0
    simpa using this
                                                           
  have hlt : ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx1 hz
                                                   
  have : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ < 1 := by simpa [hnorm_eq] using hlt
  simpa [norm] using this

lemma zetaEulerprod (s : ℂ) (hs : 1 < s.re) : Multipliable (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) ∧ riemannZeta s = ∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  have hprod : HasProd (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) (riemannZeta s) := by
    simpa using (riemannZeta_eulerProduct_hasProd (s := s) hs)
  refine And.intro ?_ ?_
  · exact hprod.multipliable
  · simpa using (hprod.tprod_eq.symm)

lemma abs_of_tprod {P : Type*} (w : P → ℂ) (hw : Multipliable w) : norm (∏' p : P, w p) = ∏' p : P, norm (w p) := by exact Multipliable.norm_tprod hw

lemma abs_P_prod (s : ℂ) (hs : 1 < s.re) : norm (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have hw : Multipliable (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := (zetaEulerprod s hs).1
  simpa using abs_of_tprod (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) hw

lemma abs_zeta_prod (s : ℂ) (hs : 1 < s.re) : norm (riemannZeta s) = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  rw [zetaEulerprod s hs |>.2, abs_P_prod s hs]

lemma abs_of_inv (z : ℂ) (_hz : z ≠ 0) : norm (z⁻¹) = (norm z)⁻¹ := norm_inv z

lemma one_minus_p_s_neq_0 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : 1 - ((p : ℕ) : ℂ) ^ (-s : ℂ) ≠ 0 := by
  intro h
  have hz : ((p : ℕ) : ℂ) ^ (-s : ℂ) = 1 := by
    simpa using (sub_eq_zero.mp h).symm
  have : (1 : ℝ) < 1 := by
    simpa [hz] using (p_s_abs_1 p s hs)
  exact (lt_irrefl (1 : ℝ)) this

lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
  norm (riemannZeta s) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹ := by
  rw [abs_zeta_prod s hs]
  congr 1
  ext p
  rw [abs_of_inv (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)) (one_minus_p_s_neq_0 p s hs)]

lemma Re2s (s : ℂ) : (2 * s).re = 2 * s.re := by simp

lemma Re2sge1 (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  rw [Re2s]
  linarith

lemma zeta_ratio_prod (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h2 := (zetaEulerprod (2 * s) (Re2sge1 s hs)).2
  have h1 := (zetaEulerprod s hs).2
  simp [h2, h1]

local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

theorem tprod_commutes_with_inclusion_infinite {α : Type*} (f : α → ℂˣ) (h : Multipliable f) :
    ι (tprod f) = tprod (fun i ↦ ι (f i)) :=
by
  change ((tprod f : ℂˣ) : ℂ) = tprod (fun i ↦ ((f i : ℂˣ) : ℂ))
  have hcont : Continuous (Units.coeHom ℂ) := by
    simpa using! (Units.continuous_val : Continuous (fun u : ℂˣ => ((u : ℂˣ) : ℂ)))
  simpa [Units.coeHom] using
    (Multipliable.map_tprod (f := f) (γ := ℂ) h (g := Units.coeHom ℂ) hcont)

theorem inclusion_commutes_with_division (a b : ℂˣ) :
    ι (a / b) = ι a / ι b := by
  exact Units.val_div_eq_div_val a b

lemma lift_multipliable_of_nonzero {P : Type*} (a : P → ℂ) (ha : Multipliable a) (h_a_nonzero : ∀ p, a p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0):
  Multipliable (fun p ↦ Units.mk0 (a p) (h_a_nonzero p)) := by

  obtain ⟨A, hA⟩ := ha
  have hA_nonzero := hA_nonzero' A hA
  refine ⟨Units.mk0 A hA_nonzero, ?_⟩
  simp [HasProd, tendsto_nhds] at hA ⊢
  intro sU h_sU_open hA_mem
  have hA_im_mem : ι (Units.mk0 A hA_nonzero) ∈ ι '' sU := Set.mem_image_of_mem ι hA_mem
  have sU_im_open : IsOpen (ι '' sU) := by
    apply (Topology.IsOpenEmbedding.isOpen_iff_image_isOpen ?_).mp
    assumption
    exact Units.isOpenEmbedding_val
  have := hA (ι '' sU) sU_im_open hA_im_mem
  obtain ⟨a1, ha⟩ := this
  use a1
  intro b ha1
  obtain ⟨x', x'_spec_mem, x'_spec_eq⟩ := ha b ha1
  suffices x' = ∏ b ∈ b, Units.mk0 (a b) (by simp [*]) by
    rwa [← this]
  have : Units.mk0 (ι x') (Units.ne_zero x') = x' :=
    Units.mk0_val x' (Units.ne_zero x')
  have this2 : (Units.mk0 (∏ b ∈ b, a b)
    (Finset.prod_ne_zero_iff.mpr fun a a_1 => h_a_nonzero a)) = x' :=
      Units.ext (id (Eq.symm x'_spec_eq))
  rw [Units.mk0_prod] at this2
  rw [←this2]
  conv =>
    rhs
    rw [← Finset.prod_attach]

lemma prod_of_ratios_simplified {P : Type*} (a b : P → ℂ)
(ha : Multipliable a) (hb : Multipliable b)
    (h_a_nonzero : ∀ p, a p ≠ 0) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ A, HasProd b A → A ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                                      
  let a' : P → ℂˣ := fun p ↦ Units.mk0 (a p) (h_a_nonzero p)
  let b' : P → ℂˣ := fun p ↦ Units.mk0 (b p) (h_b_nonzero p)

  have h_multipliable_a' : Multipliable a' := lift_multipliable_of_nonzero a ha h_a_nonzero hA_nonzero'
  have h_multipliable_b' : Multipliable b' := lift_multipliable_of_nonzero b hb h_b_nonzero hB_nonzero'
  have h_multipliable_a'_div_b' : Multipliable (fun p ↦ a' p / b' p) := Multipliable.div h_multipliable_a' h_multipliable_b'

  calc
    (∏' p, a p) / (∏' p, b p)
                                                         
    _ = (∏' p, ι (a' p)) / (∏' p, ι (b' p)) := by simp [a', b']
                                                                             
    _ = ι (∏' p, a' p) / ι (∏' p, b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                              
    _ = ι ((∏' p, a' p) / (∏' p, b' p)) := by rw [← inclusion_commutes_with_division]
                                                                                                        
    _ = ι (∏' p, a' p / b' p) := by simp [Multipliable.tprod_div, *]
                                                                           
    _ = ∏' p, ι (a' p / b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                                                   
    _ = ∏' p, (ι (a' p) / ι (b' p)) := by simp
                                                                         
    _ = ∏' p, a p / b p := by simp [a', b']

lemma prod_of_ratios {P : Type*} (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ B, HasProd b B → B ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                         
  by_cases h_a_zero : ∃ p, a p = 0
  case pos =>

    have lhs_zero : ∏' p : P, a p = 0 := by
                                                                      
      exact tprod_of_exists_eq_zero h_a_zero
    have rhs_zero : ∏' p : P, (a p / b p) = 0 := by
                                                        
      obtain ⟨p₀, hp₀⟩ := h_a_zero
      have h_div_zero : ∃ p, (a p / b p) = 0 := by
        use p₀
        simp [hp₀]
      exact tprod_of_exists_eq_zero h_div_zero
    simp [lhs_zero, rhs_zero]
  case neg =>
                                  
    push Not at h_a_zero
                                                                          
    exact prod_of_ratios_simplified a b ha hb h_a_zero h_b_nonzero hA_nonzero' hB_nonzero'

lemma simplify_prod_ratio (s : ℂ) (hs : 1 < s.re) : (∏' p : ℙ, (1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - (p : ℂ) ^ (-s : ℂ))⁻¹) = ∏' p : ℙ, ((1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - (p : ℂ) ^ (-s : ℂ))⁻¹) := by
                                                                                   
  let a := fun p : ℙ => (1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹
  let b := fun p : ℙ => (1 - (p : ℂ) ^ (-s : ℂ))⁻¹

  have ha : Multipliable a := (zetaEulerprod (2 * s) (Re2sge1 s hs)).1
  have hb : Multipliable b := (zetaEulerprod s hs).1

  have h_b_nonzero : ∀ p, b p ≠ 0 := by
    intro p
    exact inv_ne_zero (one_minus_p_s_neq_0 p s hs)

  exact prod_of_ratios a b ha hb h_b_nonzero (by
    intro A hA
                                 
    have h_eq : A = riemannZeta (2 * s) := by
      have h : HasProd a (riemannZeta (2 * s)) := by
        simpa [a] using riemannZeta_eulerProduct_hasProd (s := 2 * s) (by simp; linarith)
      exact HasProd.unique hA h
    rw [h_eq]
    exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  ) (by
  intro B hB
                                      
  have h_eq : B = riemannZeta s := by
    have h : HasProd b (riemannZeta s) := by
      simpa [b] using riemannZeta_eulerProduct_hasProd (s := s) hs
    exact HasProd.unique hB h
  rw [h_eq]
  exact riemannZeta_ne_zero_of_one_lt_re hs
  )

lemma zeta_ratios (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, ((1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h1 := zeta_ratio_prod s hs
  have h2 := simplify_prod_ratio s hs
  exact h1.trans h2

lemma diff_of_squares (z : ℂ) : 1 - z^2 = (1 - z) * (1 + z) := by ring

lemma one_sub_ne_zero_of_abs_lt_one (z : ℂ) (hz : norm z < 1) : 1 - z ≠ 0 := by
  intro h
  have h1 : 1 = z := by
    have := congrArg (fun w : ℂ => w + z) h
    simpa [sub_add_cancel, zero_add] using this
  have habs1lt : norm (1 : ℂ) < 1 := by simpa [h1] using hz
  have hnorm1lt : ‖(1 : ℂ)‖ < 1 := by simp [norm] at habs1lt
  have : (1 : ℝ) < 1 := by simp [norm_one] at hnorm1lt
  exact (lt_irrefl _) this

lemma one_add_ne_zero_of_abs_lt_one (z : ℂ) (hz : norm z < 1) : 1 + z ≠ 0 := by
  have hz' : norm (-z) < 1 := by
    simpa [norm, norm_neg] using hz
  simpa [sub_eq_add_neg] using one_sub_ne_zero_of_abs_lt_one (-z) hz'

lemma inv_mul_div_cancel_right_of_ne_zero (a b : ℂ) (ha : a ≠ 0) : ((a * b)⁻¹) / a⁻¹ = b⁻¹ := by
  simp [div_eq_mul_inv, inv_inv, mul_inv_rev, mul_comm, ha]

lemma ratio_invs (z : ℂ) (hz : norm z < 1) : (1 - z^2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_abs_lt_one z hz
  simpa [diff_of_squares z] using
    inv_mul_div_cancel_right_of_ne_zero (1 - z) (1 + z) hz1

lemma complex_cpow_neg_two_mul (z w : ℂ) (_hz : z ≠ 0) : z^(-(2*w)) = (z^(-w))^2 := by
  have h1 : -(2*w) = 2*(-w) := by ring
  rw [h1]
  have h2 : (2 : ℂ)*(-w) = ((2 : ℕ) : ℂ)*(-w) := by norm_cast
  rw [h2, Complex.cpow_nat_mul]

theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  rw [zeta_ratios s hs]; congr 1; ext p
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by rw [ne_eq, Nat.cast_eq_zero]; exact Nat.Prime.ne_zero p.2
  have h1 : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s))^2 := complex_cpow_neg_two_mul ((p : ℕ) : ℂ) s hp
  have h2 : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  rw [h1]; exact ratio_invs (((p : ℕ) : ℂ) ^ (-s)) h2

lemma two_mul_ofReal_div_two (r : ℝ) : (2 : ℂ) * ((r : ℝ) / 2 : ℂ) = (r : ℂ) := by
  have hreal : (2 : ℝ) * (r / 2) = r := by
    calc
      (2 : ℝ) * (r / 2) = (2 : ℝ) * r / 2 := by
        have h : (2 : ℝ) * r / 2 = (2 : ℝ) * (r / 2) := by
          simpa using (mul_div_assoc (2 : ℝ) r (2 : ℝ))
        simpa using h.symm
      _ = r := by
        simp
  calc
    (2 : ℂ) * ((r : ℝ) / 2 : ℂ)
        = ((2 * (r / 2) : ℝ) : ℂ) := by
              simp
    _ = (r : ℂ) := by simp [hreal]

lemma zeta_ratio_identity_ofReal_div_two (r : ℝ) (hr : 1 < ( ((r : ℝ) / 2 : ℂ) ).re) : riemannZeta (r : ℂ) / riemannZeta ((r / 2 : ℝ) : ℂ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((r : ℝ) / 2) : ℂ)))⁻¹ := by
  have h := zeta_ratio_identity (((r : ℝ) / 2 : ℂ)) hr
  simpa [two_mul_ofReal_div_two r] using h

lemma zeta_ratio_at_3_2 : riemannZeta 3 / riemannZeta ((3 : ℝ) / 2) = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := by
  have hr : 1 < (((3 : ℝ) / 2 : ℂ)).re := by
    simpa using (by norm_num : (1 : ℝ) < (3 : ℝ) / 2)
  simpa using zeta_ratio_identity_ofReal_div_two (3 : ℝ) hr

lemma triangle_inequality_specific (z : ℂ) : norm (1 - z) ≤ 1 + norm z := by
  simpa [sub_eq_add_neg, norm_one, norm_neg] using (norm_add_le (1 : ℂ) (-z))

lemma re_neg_eq_neg_re (s : ℂ) : (-s).re = - s.re := by
  simp

lemma abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : norm ((x : ℂ) ^ y) = x ^ y.re := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx y

lemma abs_p_pow_s (p : ℙ) (s : ℂ) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) = ((p : ℕ) : ℝ) ^ (-s.re : ℝ) := by
  have hx : 0 < ((p : ℕ) : ℝ) := by
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))
  simpa [Complex.ofReal_natCast, re_neg_eq_neg_re] using
    (abs_cpow_eq_rpow_re_of_pos hx (-s))

lemma abs_term_bound (p : ℙ) (t : ℝ) :
  norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) ≤ 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
                                                              
  have h1 := triangle_inequality_specific (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)))
                                                                                    
  have h2 := abs_p_pow_s p (((3 : ℝ) / 2) + t * Complex.I)
                                  
  have h3 : (((3 : ℝ) / 2) + t * Complex.I).re = ((3 : ℝ) / 2) := by simp [Complex.add_re, Complex.ofReal_re]
                                    
  have h4 : -(((3 : ℝ) / 2) + t * Complex.I).re = -((3 : ℝ) / 2) := by rw [h3]
                       
  have h5 : norm (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) = ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
    rw [h2, h4]
                
  rw [h5] at h1
  exact h1

lemma inv_inequality {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  simpa [one_div] using (one_div_le_one_div_of_le ha hab)

lemma eq_of_one_sub_eq_zero (z : ℂ) (h : 1 - z = 0) : z = 1 := by
  rw [sub_eq_zero] at h
  exact h.symm

lemma condp32 (p : ℙ) (t : ℝ) : 1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) ≠ 0 := by
  intro h
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) = 1 := eq_of_one_sub_eq_zero _ h
  let s := ((3 : ℝ) / 2) + t * Complex.I
  have hs : 1 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero]
    norm_num
  have h_abs_lt : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  have h_s_eq : ((p : ℕ) : ℂ) ^ (-s) = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) := by simp only [s]
  rw [h_s_eq, hp_eq_one] at h_abs_lt
  have : norm (1 : ℂ) = 1 := by simp [norm]
  rw [this] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

lemma abs_term_inv_bound (p : ℙ) (t : ℝ) : (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤ (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
  have h1 := abs_term_bound p t
  have h2 := condp32 p t
  have h3 := lem_abspos _ h2
  exact inv_inequality h3 h1

open NNReal in
lemma prod_inequality {P : Type*} (a b : P → ℝ≥0) (ha : Multipliable a) (hb : Multipliable b)
  (hab : ∀ p : P, a p ≤ b p) :
  ∏' p : P, a p ≤ ∏' p : P, b p := by
  exact Multipliable.tprod_le_tprod hab ha hb

lemma multipliable_complex_abs_inv {i : Type*} (g : i → ℂ) (h_mult : Multipliable (fun i => (1 - g i)⁻¹)) (_h_nonzero : ∀ i, 1 - g i ≠ 0) : Multipliable (fun i => (norm (1 - g i))⁻¹) := by
                                                       
  have h_eq : (fun i => (norm (1 - g i))⁻¹) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    simp
  rw [h_eq]
                                       
  have h_norm_mult : Multipliable (fun i => ‖(1 - g i)⁻¹‖) := Multipliable.norm h_mult
  have h_norm_eq : (fun i => ‖(1 - g i)⁻¹‖) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    rw [norm_inv]
  rwa [← h_norm_eq]

lemma multipliable_positive_inv_powers (r : ℝ) (hr : 1 < r) : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹) := by
                                                                   
  have h_sum : Summable (fun p : ℙ => ((p : ℕ) : ℝ) ^ (-r)) := by
    rw [Nat.Primes.summable_rpow]
    linarith

  have h_log_sum : Summable (fun p : ℙ => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r))) := by
    exact Real.summable_log_one_add_of_summable h_sum

  have h_log_inv_sum : Summable (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) := by
    have h_eq : (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) =
                (fun p : ℙ => -(Real.log (1 + ((p : ℕ) : ℝ) ^ (-r)))) := by
      ext p
      rw [Real.log_inv]
    rw [h_eq]
    exact Summable.neg h_log_sum

  have h_pos : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    intro p
    apply inv_pos.mpr
    have h_ge : 0 ≤ ((p : ℕ) : ℝ) ^ (-r) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith

  exact Real.multipliable_of_summable_log h_pos h_log_inv_sum

lemma hasProd_map_nnreal_coe {i : Type*} (f : i → NNReal) (a : NNReal) (h : HasProd f a) : HasProd (fun i => (f i : ℝ)) ((a : NNReal) : ℝ) := by
  have hcont : Continuous (⇑NNReal.toRealHom) := by
    rw [NNReal.coe_toRealHom]
    exact NNReal.continuous_coe
  exact HasProd.map h NNReal.toRealHom hcont

lemma multipliable_nnreal_coe {i : Type*} (f : i → NNReal) (hf : Multipliable f) : Multipliable (fun i => (f i : ℝ)) := by
                                              
  obtain ⟨a, ha⟩ := hf
                                                                         
  have h_coe := hasProd_map_nnreal_coe f a ha
                                                         
  exact ⟨(a : ℝ), h_coe⟩

lemma nnreal_coe_tprod_eq {i : Type*} (f : i → NNReal) (_hf : Multipliable f) : (∏' i : i, f i : ℝ) = ∏' i : i, (f i : ℝ) := by
  rfl

lemma hasProd_nonneg_of_pos {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (a : ℝ) (ha : HasProd f a) : 0 ≤ a := by
                                     
  have h_pos : ∀ s : Finset i, 0 < ∏ i ∈ s, f i := fun s => Finset.prod_pos (fun i _ => hpos i)
                                                         
  have h_nonneg : ∀ s : Finset i, 0 ≤ ∏ i ∈ s, f i := fun s => le_of_lt (h_pos s)
                                                 
  exact ge_of_tendsto ha (Filter.Eventually.of_forall h_nonneg)

lemma tendsto_finprod_coe_iff_tendsto_coe_finprod {i : Type*} (f : i → NNReal) (a : NNReal) :
  Filter.Tendsto (fun s => ∏ i ∈ s, (f i : ℝ)) Filter.atTop (𝓝 (a : ℝ)) ↔
  Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) Filter.atTop (𝓝 (a : ℝ)) := by
                                                                                           
  have h_comp : ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) = (fun s => ↑(∏ i ∈ s, f i)) := by
    rfl
                                                                  
  have h_eq : (fun s => ∏ i ∈ s, (f i : ℝ)) = (fun s => ↑(∏ i ∈ s, f i)) := by
    ext s
    exact (NNReal.coe_prod s f).symm
                                                                   
  rw [h_comp, ← h_eq]

lemma pnt_nnreal_isEmbedding_coe : Topology.IsEmbedding (fun x : NNReal => (x : ℝ)) := by
  refine ⟨?_, NNReal.coe_injective⟩
                                                              
  exact Topology.IsInducing.subtypeVal

lemma HasProd.of_coe_hasProd {i : Type*} (f : i → NNReal) (a : NNReal) (h : HasProd (fun i => (f i : ℝ)) (a : ℝ)) : HasProd f a := by
                                                                                     
  have h_comp : Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ (fun s => ∏ i ∈ s, f i)) Filter.atTop (𝓝 (a : ℝ)) := by
    rw [← tendsto_finprod_coe_iff_tendsto_coe_finprod]
    exact h

  have h_embed : Topology.IsEmbedding (fun x : NNReal => (x : ℝ)) := pnt_nnreal_isEmbedding_coe

  exact h_embed.tendsto_nhds_iff.mpr h_comp

lemma hasProd_nnreal_of_coe {i : Type*} (g : i → NNReal) (b : NNReal) (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  exact HasProd.of_coe_hasProd g b h

lemma multipliable_real_to_nnreal {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (h_mult : Multipliable f) : Multipliable (fun i => ⟨f i, le_of_lt (hpos i)⟩ : i → NNReal) := by
                                         
  obtain ⟨a, ha⟩ := h_mult
                                                            
  have ha_nonneg : 0 ≤ a := hasProd_nonneg_of_pos f hpos a ha
                                   
  let a_nnreal : NNReal := ⟨a, ha_nonneg⟩
                                                           
  have h_coe_eq : (fun i => ((⟨f i, le_of_lt (hpos i)⟩ : NNReal) : ℝ)) = f := by
    ext i
    rfl
                                                             
  have ha_coe : HasProd (fun i => ((⟨f i, le_of_lt (hpos i)⟩ : NNReal) : ℝ)) (a_nnreal : ℝ) := by
    rw [h_coe_eq]
    simp only [a_nnreal]
    exact ha
                                                        
  have ha_nnreal : HasProd (fun i => ⟨f i, le_of_lt (hpos i)⟩) a_nnreal :=
    hasProd_nnreal_of_coe (fun i => ⟨f i, le_of_lt (hpos i)⟩) a_nnreal ha_coe
                                                  
  exact ⟨a_nnreal, ha_nnreal⟩

lemma nnreal_coe_tprod_eq_tprod_coe {i : Type*} (f : i → NNReal) (hf : Multipliable f) :
  ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) := by
                                                                  
  have h_prod : HasProd f (∏' i, f i) := Multipliable.hasProd hf
                                                                               
  have h_map : HasProd (NNReal.toRealHom ∘ f) (NNReal.toRealHom (∏' i, f i)) :=
    HasProd.map h_prod NNReal.toRealHom NNReal.continuous_coe
                                                                                                     
  have h_comp : NNReal.toRealHom ∘ f = fun i => (↑(f i) : ℝ) := by
    ext i
    rfl
  have h_val : NNReal.toRealHom (∏' i, f i) = ↑(∏' i, f i) := rfl
                              
  rw [h_comp, h_val] at h_map
                                             
  exact HasProd.tprod_eq h_map

lemma nnreal_tprod_le_coe {i : Type*} (f g : i → NNReal) (hf : Multipliable f) (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) : ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
                                                               
  rw [nnreal_coe_tprod_eq_tprod_coe f hf, nnreal_coe_tprod_eq_tprod_coe g hg]
                                                                                               
  exact NNReal.coe_le_coe.mpr h

lemma abs_zeta_inequality (t : ℝ) :
  ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤
  ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by

  have h_pos_left : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    intro p
    apply inv_pos.mpr
    apply add_pos zero_lt_one
                                                             
    apply Real.rpow_pos_of_pos
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))

  have h_pos_right : ∀ p : ℙ, 0 < (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    intro p
    apply inv_pos.mpr
                                                            
    rw [norm_pos_iff]
    exact condp32 p t

  have h_mult_left : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹) :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)

  have h_mult_right : Multipliable (fun p : ℙ => (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹) := by
    let s := ((3 : ℝ) / 2) + t * Complex.I
    have hs : 1 < s.re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero]
      norm_num
                                               
    have h_euler := (zetaEulerprod s hs).1
    have h_nonzero : ∀ p : ℙ, 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := fun p => condp32 p t
    exact multipliable_complex_abs_inv (fun p : ℙ => ((p : ℕ) : ℂ) ^ (-s)) h_euler h_nonzero

  let f : ℙ → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹, le_of_lt (h_pos_left p)⟩
  let g : ℙ → NNReal := fun p => ⟨(norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹, le_of_lt (h_pos_right p)⟩

  have hf : Multipliable f := multipliable_real_to_nnreal _ h_pos_left h_mult_left
  have hg : Multipliable g := multipliable_real_to_nnreal _ h_pos_right h_mult_right

  have h_pointwise : ∀ p : ℙ, f p ≤ g p := by
    intro p
    simp only [f, g]
    exact abs_term_inv_bound p t

  have h_nnreal_ineq : ∏' p, f p ≤ ∏' p, g p := prod_inequality f g hf hg h_pointwise

  have h_convert : ∏' p, (f p : ℝ) ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg h_nnreal_ineq

  have h_eq_f : ∏' p, (f p : ℝ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    rfl

  have h_eq_g : ∏' p, (g p : ℝ) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
    rfl

  rw [h_eq_f, h_eq_g] at h_convert
  exact h_convert

lemma abs_zeta_ratio_eval : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
                                                 
  have hratio := zeta_ratio_at_3_2
                                          
  let w : ℙ → ℂ := fun p => (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹
  let u : ℙ → ℝ := fun p => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹
                                        
  have hu_mult : Multipliable u :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)
                                        
  have hw_eq : w = fun p : ℙ => (u p : ℂ) := by
    funext p
                                                                               
    have hx : 0 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (p : ℕ))
    have hcpow : (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ)
        = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)) := by
      simpa using (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hx) (y := -((3 : ℝ) / 2)))
    calc
      w p = (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := rfl
      _ = (1 + (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ))⁻¹ := by
        simp [hcpow]
      _ = (((1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ : ℝ) : ℂ) := by
        simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]
                                                                 
  have hw_mult : Multipliable w := by
    have hmap : Multipliable ((fun x : ℝ => (x : ℂ)) ∘ u) :=
      Multipliable.map (hf := hu_mult) Complex.ofRealHom Complex.continuous_ofReal
    simpa [hw_eq] using! hmap
                                            
  have h_abs_tprod : norm (∏' p : ℙ, w p) = ∏' p : ℙ, norm (w p) :=
    abs_of_tprod w hw_mult
                                                               
  have h_abs_eq_fun : (fun p : ℙ => norm (w p)) = u := by
    funext p
              
    have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
    have hpos : 0 < 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by linarith
    have hnonneg : 0 ≤ u p := by
      have : 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := inv_pos.mpr hpos
      exact this.le
               
    simp [hw_eq, Complex.norm_real, abs_of_nonneg hnonneg]
                                                        
  have h_abs_ratio : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
      = norm (∏' p : ℙ, w p) := by
    simpa [w] using congrArg norm hratio
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = norm (∏' p : ℙ, w p) := h_abs_ratio
    _ = ∏' p : ℙ, norm (w p) := h_abs_tprod
    _ = ∏' p : ℙ, u p := by simp [h_abs_eq_fun]
    _ = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := rfl

theorem zeta_lower_bound (t : ℝ) :
  norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) ≤
    norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  have hs : 1 < (((3 : ℝ) / 2 : ℂ) + t * Complex.I).re := by
    simp only [Complex.add_re, Complex.mul_I_re]
    norm_num
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := abs_zeta_ratio_eval
    _ ≤ ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ :=
          abs_zeta_inequality t
    _ = norm (riemannZeta (((3 : ℝ) / 2 : ℂ) + t * Complex.I)) := by
          simpa using (abs_zeta_prod_prime (((3 : ℝ) / 2 : ℂ) + t * Complex.I) hs).symm

lemma summable_one_div_nat_add_rpow' {x : ℝ} (hx : 1 < x) : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) x).2 hx
  have h' : Summable (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) := by
    simpa [one_div] using h
  have h2 : (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) = (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      exact add_nonneg this (show 0 ≤ (1 : ℝ) from zero_le_one)
    simp [abs_of_nonneg hn]
  have h'' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    simpa [h2] using h'
  have h''' : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ x)⁻¹) := by
    simpa [Nat.cast_add] using h''
  simpa [one_div] using h'''

lemma tsum_pos_of_pos_first_term {f : ℕ → ℝ} (hf : Summable f) (h0 : 0 < f 0) (hnonneg : ∀ n, 0 ≤ f n) : 0 < ∑' n, f n := by
  have hsum0 : ∑ n ∈ Finset.range 1, f n = f 0 := by
    simp
  have hpos_partial : 0 < ∑ n ∈ Finset.range 1, f n := by
    simpa [hsum0] using h0
  have hsumle : ∑ n ∈ Finset.range 1, f n ≤ ∑' n, f n := by
    have hnonneg' : ∀ n ∉ Finset.range 1, 0 ≤ f n := by
      intro n hn
      exact hnonneg n
    simpa using (hf.sum_le_tsum (s := Finset.range 1) hnonneg')
  exact lt_of_lt_of_le hpos_partial hsumle

lemma first_term_pos (x : ℝ) : 0 < (1 : ℝ) / ((1 : ℝ) ^ x) := by
  simp [Real.one_rpow]

lemma terms_nonneg (x : ℝ) : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n + 1 : ℝ) ^ x) := by
  intro n
  have hposb' : 0 < ((n : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n)) zero_lt_one
  have hposb : 0 < ((n + 1 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hposb'
  have hdenpos : 0 < ((n + 1 : ℝ) ^ x) := by
    simpa using (Real.rpow_pos_of_pos hposb x)
  have hden_nonneg : 0 ≤ ((n + 1 : ℝ) ^ x) := le_of_lt hdenpos
  have hnum_nonneg : 0 ≤ (1 : ℝ) := le_of_lt (zero_lt_one : 0 < (1 : ℝ))
  exact div_nonneg hnum_nonneg hden_nonneg

lemma term_eq_ofRealC (x : ℝ) (n : ℕ) : (1 / ((n + 1 : ℂ) ^ (x : ℂ))) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
  have hbase_nonneg : 0 ≤ (n + 1 : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : 0 ≤ (n : ℝ) + 1 := add_nonneg hn (show 0 ≤ (1 : ℝ) from zero_le_one)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hpow' : ((n + 1 : ℂ) ^ (x : ℂ)) = (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (x := (n + 1 : ℝ)) (hx := hbase_nonneg) (y := x)).symm
  have hdiv : (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
    simp
  calc
    1 / ((n + 1 : ℂ) ^ (x : ℂ))
        = (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by simp [hpow']
    _ = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := hdiv

lemma zeta_eq_ofReal (x : ℝ) (hx : 1 < x) :
  riemannZeta x = ((∑' n : ℕ, ((1 : ℝ) / ((n + 1 : ℝ) ^ x))) : ℝ) := by
                              
  have h1 : riemannZeta (x : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
    apply zeta_eq_tsum_one_div_nat_add_one_cpow
    simpa using hx
                                             
  have h2 : ∀ n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
    exact fun n => term_eq_ofRealC x n
                             
  rw [h1]
  simp_rw [h2]
                                         
  rw [← Complex.ofReal_tsum]

lemma term_inv_eq_ofRealC (x : ℝ) (n : ℕ) : ((n + 1 : ℂ) ^ (x : ℂ))⁻¹ = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
  rw [inv_eq_one_div]
  simpa using (term_eq_ofRealC x n)

lemma im_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).im = 0 := by
  have him := congrArg Complex.im (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  have hz : (((∑' n : ℕ, g n) : ℝ) : ℂ).im = 0 := by
    simp
  exact Eq.trans him hz

lemma re_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).re = ∑' n : ℕ, g n := by
  have h := congrArg Complex.re (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  simpa [Complex.ofReal_re] using h

lemma zetapos (x : ℝ) (hx : 1 < x) : (riemannZeta x).im = 0 ∧ 0 < (riemannZeta x).re := by
  have hxC : 1 < (Complex.ofReal x).re := by simpa [Complex.ofReal_re] using hx
  have hz : riemannZeta (x : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (s := (x : ℂ)) hxC
  have him : (riemannZeta x).im = 0 := by
    simpa [hz, term_eq_ofRealC x] using
      (im_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hre : (riemannZeta x).re = ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) := by
    simpa [hz, term_eq_ofRealC x] using
      (re_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) :=
    summable_one_div_nat_add_rpow' (x := x) hx
  have hpos0 : 0 < 1 / ((Nat.cast 0 + 1 : ℝ) ^ x) := by
    simp [zero_add]
  have hnonneg : ∀ n : ℕ, 0 ≤ 1 / ((n + 1 : ℝ) ^ x) := terms_nonneg x
  have hpos : 0 < ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) :=
    tsum_pos_of_pos_first_term hsum hpos0 hnonneg
  exact ⟨him, by simpa [hre] using hpos⟩

lemma zeta332pos : 0 < norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have h32 : (1 : ℝ) < (3 : ℝ) / 2 := by norm_num
  obtain ⟨h3im, h3repos⟩ := zetapos 3 h3
  obtain ⟨h32im, h32repos⟩ := zetapos ((3 : ℝ) / 2) h32
  have h3ne : riemannZeta (3 : ℝ) ≠ 0 := by
    intro hz
    exact (ne_of_gt h3repos) (by simpa using congrArg Complex.re hz)
  have h32ne : riemannZeta ((3 : ℝ) / 2) ≠ 0 := by
    intro hz
    exact (ne_of_gt h32repos) (by simpa using congrArg Complex.re hz)
  have hdivne : riemannZeta (3 : ℝ) / riemannZeta ((3 : ℝ) / 2) ≠ 0 :=
    div_ne_zero h3ne h32ne
  simpa using (norm_pos_iff.mpr hdivne)

lemma zeta_low_332 : ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, a ≤ norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  use norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
  exact ⟨zeta332pos, zeta_lower_bound⟩

open Real _root_.Set Filter Topology MeasureTheory
open scoped BigOperators Topology

lemma one_div_nat_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) : 1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · have hcalc : 1 / (n : ℂ) ^ s = (n : ℂ) ^ (-s) := by
      calc
        1 / (n : ℂ) ^ s = ((n : ℂ) ^ s)⁻¹ := by simp [one_div]
        _ = (n : ℂ) ^ (-s) := by simpa using (Complex.cpow_neg (n : ℂ) s).symm
    simpa [h] using hcalc

lemma lem_zetaLimit (s : ℂ) (hs : 1 < s.re) : riemannZeta s = ∑' n : ℕ, if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  classical
  have hsne : s ≠ 0 := by
    intro h
    have hpos : 0 < s.re := lt_trans (show (0 : ℝ) < 1 from zero_lt_one) hs
    have hne : s.re ≠ 0 := ne_of_gt hpos
    simp [h] at hne
  have hz : riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hz

noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

lemma sum_Icc1_eq_sum_range_succ (N : ℕ) (g : ℕ → ℂ) :
  (∑ k ∈ Finset.Icc 1 N, g k) = ∑ n ∈ Finset.range N, g (n + 1) := by
  classical
                                                                  
  symm
  refine Finset.sum_bij (s := Finset.range N) (t := Finset.Icc 1 N)
    (f := fun n => g (n + 1)) (g := fun k => g k)
    (i := fun n (_hn : n ∈ Finset.range N) => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := Finset.mem_range.mp hn
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have h2 : n + 1 ≤ N := Nat.succ_le_of_lt hlt
    exact (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  · intro a ha b hb h
                             
    simpa using Nat.succ_injective h
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, ?_, ?_⟩
    ·                      
      have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      have hle : (k - 1) + 1 ≤ N := by simpa [hsucc] using hk2
      have hlt : k - 1 < N := lt_of_lt_of_le (Nat.lt_succ_self (k - 1)) hle
      exact Finset.mem_range.mpr hlt
    ·                  
      simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

lemma sum_Icc0_eq_sum_Icc1_of_zero (N : ℕ) (g : ℕ → ℂ) (h0 : g 0 = 0) :
  (∑ k ∈ Finset.Icc 0 N, g k) = ∑ k ∈ Finset.Icc 1 N, g k := by
  classical
  have hdecomp : insert (0 : ℕ) (Finset.Icc 1 N) = Finset.Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N))
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 N := by
    intro h
    rcases Finset.mem_Icc.mp h with ⟨h1, _h2⟩
    have : ¬ (1 ≤ (0 : ℕ)) := by decide
    exact this h1
  calc
    (∑ k ∈ Finset.Icc 0 N, g k)
        = ∑ k ∈ insert 0 (Finset.Icc 1 N), g k := by
            simp [hdecomp]
    _ = g 0 + ∑ k ∈ Finset.Icc 1 N, g k := by
            simp
    _ = ∑ k ∈ Finset.Icc 1 N, g k := by simp [h0]

lemma sum_Icc0_shifted_eq_sum_range (a : ℕ → ℂ) (m : ℕ) :
  (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range m, a (n + 1) := by
  classical
  calc
    (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k))
        = ∑ k ∈ Finset.Icc 1 m, (if k = 0 then 0 else a k) := by
          simpa using
            (sum_Icc0_eq_sum_Icc1_of_zero (N := m)
              (g := fun k => (if k = 0 then 0 else a k)) (h0 := by simp))
    _ = ∑ n ∈ Finset.range m, (if n + 1 = 0 then 0 else a (n + 1)) := by
          simpa using
            (sum_Icc1_eq_sum_range_succ (N := m) (g := fun k => (if k = 0 then 0 else a k)))
    _ = ∑ n ∈ Finset.range m, a (n + 1) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp

lemma sum_Icc0_shifted_floor_eq (a : ℕ → ℂ) (t : ℝ) :
  (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range ⌊t⌋₊, a (n + 1) := by
  simpa using (sum_Icc0_shifted_eq_sum_range a ⌊t⌋₊)

lemma helper_contdiff_differentiable_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
  (a b : ℝ) :
  (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) ∧ IntegrableOn (deriv f) (Set.Icc a b) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcont_deriv : Continuous (deriv f) := hf.continuous_deriv le_rfl
  refine And.intro ?hdiffAt ?hint
  · intro t ht
    have hdt : DifferentiableAt ℝ f t := hdiff.differentiableAt
    exact hdt
  ·                                                          
    have hcontOn : ContinuousOn (deriv f) (Set.Icc a b) := hcont_deriv.continuousOn
    exact hcontOn.integrableOn_compact isCompact_Icc

lemma sum_range_mul_shift_comm (N : ℕ) (a : ℕ → ℂ) (f : ℝ → ℂ) :
  (∑ n ∈ Finset.range N, f (n + 1) * (if n + 1 = 0 then 0 else a (n + 1)))
    = ∑ n ∈ Finset.range N, a (n + 1) * f (n + 1) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_comm]

lemma sum_range_shifted_coeffs (N : ℕ) (a c : ℕ → ℂ) (f : ℝ → ℂ)
  (hshift : ∀ n, c (n + 1) = a (n + 1)) :
  (∑ n ∈ Finset.range N, f (↑(n + 1)) * c (n + 1))
    = ∑ n ∈ Finset.range N, f (↑(n + 1)) * a (n + 1) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  simp [hshift n]

lemma sum_range_commute_mul (N : ℕ) (a : ℕ → ℂ) (f : ℝ → ℂ) :
  (∑ n ∈ Finset.range N, f (↑(n + 1)) * a (n + 1))
    = ∑ n ∈ Finset.range N, a (n + 1) * f (↑(n + 1)) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_comm]

lemma lem_abelSummation {a : ℕ → ℂ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (N : ℕ) (hN : 1 ≤ N) :
    (let A := fun u : ℝ => ∑ n ∈ Finset.range (Nat.floor u), a (n + 1);
      ∑ n ∈ Finset.range N, a (n + 1) * f (n + 1)
        = (A N) * f N - ∫ u in (1 : ℝ)..N, (A u) * deriv f u) := by
  classical
                                                                     
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else a k
                                                                        
  set A : ℝ → ℂ := fun u : ℝ => ∑ n ∈ Finset.range (Nat.floor u), a (n + 1) with hA
                                                                          
  have hdiff_int := helper_contdiff_differentiable_integrable (f := f) hf (1 : ℝ) N
  rcases hdiff_int with ⟨hdiff, hint⟩
                                                                             
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (m := N)
      (hc := by simp [c])
      (hf_diff := by
        intro t ht
        simpa using (hdiff t ht))
      (hf_int := by simpa using hint)
                                                                              
  have hLHS :
      (∑ k ∈ Finset.Icc 0 N, f k * c k)
        = ∑ n ∈ Finset.range N, a (n + 1) * f (n + 1) := by
                                                
    have h0 :
        (∑ k ∈ Finset.Icc 0 N, f k * c k)
          = ∑ k ∈ Finset.Icc 1 N, f k * c k := by
      simpa [c] using
        (sum_Icc0_eq_sum_Icc1_of_zero (N := N)
          (g := fun k => f k * c k) (h0 := by simp [c]))
                                     
    have h1 :
        (∑ k ∈ Finset.Icc 1 N, f k * c k)
          = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by
      simpa using
        (sum_Icc1_eq_sum_range_succ (N := N) (g := fun k => f k * c k))
                                                    
    have h2 :
        (∑ n ∈ Finset.range N, f (n + 1) * c (n + 1))
          = ∑ n ∈ Finset.range N, a (n + 1) * f (n + 1) := by
      simpa [c] using (sum_range_mul_shift_comm (N := N) (a := a) (f := f))
              
    simp [h0, h1, h2]
                                                        
  have hAN : A N = ∑ n ∈ Finset.range N, a (n + 1) := by
    have : (Nat.floor (N : ℝ)) = N := by
      simp
    simp [hA, this]
  have hMain :
      f N * (∑ k ∈ Finset.Icc 0 N, c k) = (A N) * f N := by
                                                                    
    have hs : (∑ k ∈ Finset.Icc 0 N, c k) = ∑ n ∈ Finset.range N, a (n + 1) := by
      simpa [c] using (sum_Icc0_shifted_eq_sum_range (a := a) (m := N))
    calc
      f N * (∑ k ∈ Finset.Icc 0 N, c k)
          = (∑ k ∈ Finset.Icc 0 N, c k) * f N := by simp [mul_comm]
      _ = (∑ n ∈ Finset.range N, a (n + 1)) * f N := by simp [hs]
      _ = (A N) * f N := by simp [hAN]
                                                                             
  have hInt :
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (A u) * deriv f u := by
                                               
    have hfun :
        (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
          = (fun t => deriv f t * A t) := by
      funext t
      have : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = A t := by
        simpa [c, hA] using (sum_Icc0_shifted_floor_eq (a := a) (t := t))
      simp [this]
                                                                                   
    have h1Nℝ : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hI :
        (∫ u in (1 : ℝ)..N, (A u) * deriv f u)
          = ∫ u in Set.Ioc (1 : ℝ) N, (A u) * deriv f u := by
      simpa using
        (intervalIntegral.integral_of_le
          (f := fun u => (A u) * deriv f u) (μ := volume) h1Nℝ)
    calc
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
          = ∫ t in Set.Ioc (1 : ℝ) N, deriv f t * A t := by
                simp [hfun]
      _ = ∫ t in Set.Ioc (1 : ℝ) N, (A t) * deriv f t := by
                simp [mul_comm]
      _ = ∫ u in (1 : ℝ)..N, (A u) * deriv f u := by
                simp [hI]
                                                                             
  have hfinal : ∑ n ∈ Finset.range N, a (n + 1) * f (n + 1)
      = (A N) * f N - ∫ u in (1 : ℝ)..N, (A u) * deriv f u := by

    simpa [hLHS, hMain, hInt]
      using habel
                                                                           
  simpa [hA] using hfinal

lemma lem_partialSumIsZetaN (s : ℂ) (N : ℕ) :
    (let f := fun u : ℝ => (u : ℂ) ^ (-s)
     let a := fun _n : ℕ => (1 : ℂ)
     zetaPartialSum s N = ∑ n ∈ Finset.range N, a n * f (n + 1)) := by
  simp [zetaPartialSum]

lemma lem_sumOfAn (u : ℝ) (_hu : 1 ≤ u) :
    (let a := fun _n : ℕ => (1 : ℂ)
     let A := fun u : ℝ => ∑ n ∈ Finset.range (Nat.floor u), a (n + 1)
     A u = (Nat.floor u : ℂ)) := by
  simp [Finset.sum_const, Finset.card_range]

lemma lem_fDeriv (s : ℂ) (u : ℝ) (hu : 0 < u) :
    (let f := fun u : ℝ => (u : ℂ) ^ (-s)
     deriv f u = -s * (u : ℂ) ^ (-s - 1)) := by
                             
  show deriv (fun u : ℝ => (u : ℂ) ^ (-s)) u = -s * (u : ℂ) ^ (-s - 1)
  have hu_ne_zero : u ≠ 0 := ne_of_gt hu
  by_cases h : s = 0
  ·                                
    simp [h]
  ·                                
    have hneg_s_ne_zero : -s ≠ 0 := neg_ne_zero.mpr h
    exact Complex.deriv_ofReal_cpow_const hu_ne_zero hneg_s_ne_zero

lemma differentiable_integrable_cpow_on_Icc (s : ℂ) (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) :
  (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-s)) t)
  ∧ IntegrableOn (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Icc a b) :=
by
  classical
                                                       
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  set g : ℝ → ℂ := fun u => -s * (u : ℂ) ^ (-s - 1)
                            
  have hpos_of_mem : ∀ {t : ℝ}, t ∈ Set.Icc a b → 0 < t := by
    intro t ht; exact lt_of_lt_of_le h0 ht.1
                                    
  have hdiff_at : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hs : s = 0
    ·                   
      simp [f, hs]
    ·                                                        
      have hr : (-s) ≠ 0 := by simpa using (neg_ne_zero.mpr hs)
      have hhas : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * t ^ ((-s) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s) (hr := hr)
      exact hhas.differentiableAt
                             
  have hcont_pow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hzero : (-s - 1) = 0
    ·                       
      have : (fun u : ℝ => (u : ℂ) ^ (-s - 1)) = fun _ : ℝ => (1 : ℂ) := by
        funext u; simp [hzero]
      simpa [this] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
    ·                                             
      have hr : (-s - 1) ≠ 0 := hzero
      have hcpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1)) ((-s - 1) * t ^ ((-s - 1) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s - 1) (hr := hr)
      have hcont_at : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-s - 1)) t :=
        hcpow.differentiableAt.continuousAt
      simpa using hcont_at.continuousWithinAt
  have hcont_g : ContinuousOn g (Set.Icc a b) := by
    have hconst : ContinuousOn (fun _ : ℝ => (-s : ℂ)) (Set.Icc a b) := continuousOn_const
    simpa only [g, Pi.mul_def, neg_mul] using! hconst.mul hcont_pow
                                                                                  
  have hEqOn : EqOn (deriv f) g (Set.Icc a b) := by
    intro u hu
    have hu_pos : 0 < u := hpos_of_mem hu
    simpa [f, g] using (lem_fDeriv s u hu_pos)
                                                                                                            
  have hcont_deriv : ContinuousOn (deriv f) (Set.Icc a b) := by
                                            
    have hg_restr : Continuous ((Set.Icc a b).domRestrict g) := hcont_g.domRestrict
    have hEqRestr : (Set.Icc a b).domRestrict (deriv f) = (Set.Icc a b).domRestrict g := by
      funext x; exact hEqOn x.property
    have hderiv_restr : Continuous ((Set.Icc a b).domRestrict (deriv f)) := by
      simpa [hEqRestr] using hg_restr
    simpa [continuousOn_iff_continuous_domRestrict] using hderiv_restr
                                                              
  have hInt : IntegrableOn (deriv f) (Set.Icc a b) :=
    hcont_deriv.integrableOn_compact isCompact_Icc
  exact And.intro hdiff_at hInt

lemma intervalIntegral_congr_of_Ioc_eq (a b : ℝ) (h : a ≤ b)
  (f g : ℝ → ℂ)
  (hpt : ∀ u ∈ Set.Ioc a b, f u = g u) :
  (∫ u in a..b, f u) = ∫ u in a..b, g u := by
                                                                                
  have h1 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc a b → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu; exact hpt u hu
  have hIocEmpty : Set.Ioc b a = (∅ : Set ℝ) := by
    simpa using! (Set.Ioc_eq_empty_of_le h)
  have h2 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc b a → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu
    have : u ∈ (∅ : Set ℝ) := by simp [hIocEmpty] at hu
    exact this.elim
  simpa using
    (intervalIntegral.integral_congr_ae' (a := a) (b := b) (μ := MeasureTheory.volume)
      (f := f) (g := g) h1 h2)

lemma lem_applyAbel (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  classical
                   
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
                                             
  have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiff_int :=
    differentiable_integrable_cpow_on_Icc (s := s) (a := (1 : ℝ)) (b := (N : ℝ))
      (h0 := by exact zero_lt_one) (_hle := hle)
  rcases hdiff_int with ⟨hdiff, hint⟩
                                                         
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c])
      (hf_diff := by intro t ht; simpa [f] using (hdiff t ht))
      (hf_int := by simpa [f] using hint)
                                         
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
                                    
    have h0 :
        (∑ k ∈ Finset.Icc 0 N, f k * c k) = ∑ k ∈ Finset.Icc 1 N, f k * c k := by
      simpa [c] using
        (sum_Icc0_eq_sum_Icc1_of_zero (N := N)
          (g := fun k => f k * c k) (h0 := by simp [c]))
    have h1 : (∑ k ∈ Finset.Icc 1 N, f k * c k)
                = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by
      simpa using (sum_Icc1_eq_sum_range_succ (N := N) (g := fun k => f k * c k))
    have h2 : (∑ n ∈ Finset.range N, f (n + 1) * c (n + 1))
                = ∑ n ∈ Finset.range N, f (n + 1) := by
      apply Finset.sum_congr rfl; intro n hn; simp [c]
    calc
      (∑ k ∈ Finset.Icc 0 N, f k * c k)
          = ∑ k ∈ Finset.Icc 1 N, f k * c k := by simpa using h0
      _ = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by simpa using h1
      _ = ∑ n ∈ Finset.range N, f (n + 1) := by simpa using h2
      _ = zetaPartialSum s N := by simp [zetaPartialSum, f]
                                                     
  have hset_to_interval :
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa using
      (intervalIntegral.integral_of_le
        (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        (μ := volume) hle).symm
  have hstep1 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa [hLHS, hset_to_interval] using habel
                                                
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
                                                                             
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hle)
      (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
      (g := fun u => (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)))
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hderiv : deriv f u = -s * (u : ℂ) ^ (-s - 1) := by
      simpa [f] using (lem_fDeriv s u hu_pos)
                                          
    have hsumfloor : (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k) = (Nat.floor u : ℂ) := by
      have hshift := sum_Icc0_shifted_floor_eq (a := fun _ => (1 : ℂ)) (t := u)
      have hsum : (∑ n ∈ Finset.range ⌊u⌋₊, (1 : ℂ)) = (Nat.floor u : ℂ) := by
        simp [Finset.sum_const, Finset.card_range]
      simpa [c, hsum] using hshift
    calc
      deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k
          = deriv f u * (Nat.floor u : ℂ) := by simp [hsumfloor]
      _ = (Nat.floor u : ℂ) * deriv f u := by simp [mul_comm]
      _ = (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by simp [hderiv]
                                     
  have hstep2 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    simpa [hInt_congr] using hstep1
                                                      
  have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
    have hs : (∑ k ∈ Finset.Icc 0 N, c k) = ∑ n ∈ Finset.range N, (1 : ℂ) := by
      simpa [c] using (sum_Icc0_shifted_eq_sum_range (a := fun _ => (1 : ℂ)) (m := N))
    have hsumN : (∑ n ∈ Finset.range N, (1 : ℂ)) = (N : ℂ) := by
      simp [Finset.sum_const, Finset.card_range]
    calc
      f N * (∑ k ∈ Finset.Icc 0 N, c k)
          = f N * (∑ n ∈ Finset.range N, (1 : ℂ)) := by simp [hs]
      _ = f N * (N : ℂ) := by simp [hsumN]
      _ = (N : ℂ) * f N := by simp [mul_comm]
                                     
  have hfinal :
      zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    calc
      zetaPartialSum s N
          = f N * (∑ k ∈ Finset.Icc 0 N, c k)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simpa using hstep2
      _ = (N : ℂ) * f N
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [hMain]
      _ = (N : ℂ) * (N : ℂ) ^ (-s)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [f]
  exact hfinal

lemma lem_floorNisN (N : ℕ) (_hN : 1 ≤ N) : Nat.floor (N : ℝ) = N := by simp

lemma helper_integral_const_mul (a b : ℝ) (c : ℂ) (g : ℝ → ℂ) : ∫ x in a..b, c * g x = c * ∫ x in a..b, g x := by simp

lemma helper_cpow_mul_cpow_neg_eq_cpow_sub (x s : ℂ) (hx : x ≠ 0) : x * x ^ (-s) = x ^ (1 - s) := by
  calc
    x * x ^ (-s) = x ^ (1 : ℂ) * x ^ (-s) := by
      simp [Complex.cpow_one]
    _ = x ^ (1 + (-s)) := by
      simpa using (Complex.cpow_add (x := x) (y := (1 : ℂ)) (z := (-s)) hx).symm
    _ = x ^ (1 - s) := by
      simp [sub_eq_add_neg]

lemma lem_zetaNsimplified1 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) : zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have happly := lem_applyAbel s N hN
                                               
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    simp [mul_left_comm]
  calc
    zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          simpa using happly
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          - ((-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          simp [sub_eq_add_neg, neg_mul]
    _ = (N : ℂ) ^ (1 - s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          have hpos : 0 < N := (Nat.succ_le_iff).mp hN
          have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
          have hpow := helper_cpow_mul_cpow_neg_eq_cpow_sub (x := (N : ℂ)) (s := s) hNz
          simp [hpow]

lemma lem_floorUdecomp (u : ℝ) : (Int.floor u : ℝ) = u - Int.fract u := by exact (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)

lemma lem_fracPartBound (u : ℝ) : 0 ≤ Int.fract u ∧ Int.fract u < 1 ∧ |Int.fract u| ≤ (1 : ℝ) := by
  constructor
  · exact Int.fract_nonneg u
  · constructor
    · exact Int.fract_lt_one u
    · have hnonneg : 0 ≤ Int.fract u := Int.fract_nonneg u
      have hle : Int.fract u ≤ (1 : ℝ) := le_of_lt (Int.fract_lt_one u)
      simpa [abs_of_nonneg hnonneg] using hle

lemma helper_continuousOn_cpow (r : ℂ) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) := by
  classical
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
  by_cases hr : r = 0
  ·              
    have hconst : (fun u : ℝ => (u : ℂ) ^ r) = fun _ => (1 : ℂ) := by
      funext u; simp [hr]
    simpa [hconst] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
  ·                                        
    have hderiv : HasDerivAt (fun u : ℝ => (u : ℂ) ^ r) (r * t ^ (r - 1)) t :=
      hasDerivAt_ofReal_cpow_const (x := t) (hx := ne_of_gt ht_pos) (r := r) (hr := hr)
    exact hderiv.differentiableAt.continuousAt.continuousWithinAt

lemma helper_intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                          
  have hcont1 : ContinuousOn (fun u : ℝ => (u : ℂ)) (Set.Icc a b) :=
    (Complex.continuous_ofReal).continuousOn
  have hcont2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont1.mul hcont2
                                                            
  have hint_on : IntegrableOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont.integrableOn_compact isCompact_Icc
  have hint : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
    simpa using
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
        (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2 hint_on
  exact hint

lemma helper_aestronglyMeasurable_kernel_Icc (s : ℂ) {a b : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Icc a b)) := by
                                
  have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Icc a b)) :=
    (Complex.measurable_ofReal.comp hmeas_fract).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Icc a b)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by measurability
    exact hmeas.aestronglyMeasurable
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_intervalIntegrable_frac_kernel (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                                             
  let μ := volume.restrict (Icc a b)
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
                       
  have hmeas : AEStronglyMeasurable f μ := by simpa [μ, f] using helper_aestronglyMeasurable_kernel_Icc (s := s) (a := a) (b := b)
                                  
  have hbound_ae : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
                                                  
    refine ((ae_restrict_iff' (μ := volume) (s := Icc a b)
      (p := fun u : ℝ => ‖f u‖ ≤ g u) measurableSet_Icc)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro u hu
                    
    have hfract_le1 : ‖(Int.fract u : ℝ)‖ ≤ (1 : ℝ) := by
      simpa using (lem_fracPartBound u).2.2
                           
    have : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp
    have : ‖f u‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp [f]
    have : ‖f u‖ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ :=
      le_trans this (mul_le_mul_of_nonneg_right hfract_le1 (by exact norm_nonneg _))
    simpa [g] using (by simpa [one_mul] using this)
                                             
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hg_int_on : IntegrableOn g (Icc a b) := by
    have hcont_norm : ContinuousOn g (Icc a b) := by
      simpa [g] using (hcont.norm)
    exact hcont_norm.integrableOn_compact isCompact_Icc
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  have hg : Integrable g μ := by simpa [μ] using! hg_int_on
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas hf0 hg
      (by
                                    
        have : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
          simpa [sub_eq_add_neg, norm_neg, μ, f, g] using hbound_ae
        simpa using this)
                                         
  have hf_on : IntegrableOn f (Icc a b) := by simpa [μ, f] using! hf
  simpa using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
      (f := f) hab).2 hf_on

lemma lem_integralSplit (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
                                          
  have hcongr1 :
      (∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) (le_of_lt hu.1)
    have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
      simpa using (natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu0)
    have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hfloorR
    have hIFR : (Int.floor u : ℝ) = u - Int.fract u := lem_floorUdecomp u
    have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hIFR
    have : (Nat.floor u : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := hfloorC.trans hIFC
    simp [this, sub_eq_add_neg]
                               
  have hcongr2 :
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
        = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_mul_cpow_id (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have hI2 : IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_frac_kernel (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have :
        (∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
      apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
      intro u hu; simp [sub_mul]
    calc
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := this
      _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
            - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) :=
        (intervalIntegral.integral_sub (μ := volume) (a := (1 : ℝ)) (b := (N : ℝ)) hI1 hI2)
                                              
  have hpow :
      (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu_pos
    have hcx0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
    calc
      (u : ℂ) * (u : ℂ) ^ (-s - 1)
          = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [Complex.cpow_one]
      _ = (u : ℂ) ^ (1 + (-s - 1)) := by
        simpa using
          (Complex.cpow_add (x := (u : ℂ)) (y := (1 : ℂ)) (z := (-s - 1)) hcx0).symm
      _ = (u : ℂ) ^ (-s) := by
        simp [add_left_comm, sub_eq_add_neg]
             
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := hcongr1
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := hcongr2
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
      simp [hpow]

lemma lem_zetaNsimplified2 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
  have hstep1: _ := lem_zetaNsimplified1 s N hN
  rw [lem_integralSplit] at hstep1
  rw [mul_sub] at hstep1
  rw [hstep1]
  exact (add_sub_assoc _ _ _).symm
  exact hN

lemma lem_evalMainIntegral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0notIcc : (0 : ℝ) ∉ Set.Icc (1 : ℝ) (N : ℝ) := by
    intro hx
    exact (not_le.mpr (by norm_num : (0 : ℝ) < 1)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    simp [uIcc_of_le h01leN]
  have hrne : -s ≠ (-1 : ℂ) := by
    intro h
    apply hs
    simpa using congrArg Neg.neg h
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hcond : (-1 < (-s).re) ∨ (-s ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ)) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s) hcond)
  have hmul : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
    simpa using congrArg (fun x => s * x) hint
  have hrewrite :
      s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
        = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
    have : s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
          = s * (((N : ℂ) ^ (1 - s) - (1 : ℂ) ^ (1 - s)) / (1 - s)) := by
      simp [add_comm, sub_eq_add_neg]
    have h1pow : (1 : ℂ) ^ (1 - s) = 1 := by simp
    simpa [h1pow] using this
  have hsplit : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
      = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
    have h1 : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
        = (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s) := by
      simpa using (mul_div_assoc s ((N : ℂ) ^ (1 - s) - 1) (1 - s)).symm
    have h2 : (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s)
        = (s / (1 - s)) * ((N : ℂ) ^ (1 - s) - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_mul_eq_mul_div (a := s) (b := (1 - s)) (c := ((N : ℂ) ^ (1 - s) - 1))).symm
    exact h1.trans h2
  calc
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
        = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := hmul
    _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := hrewrite
    _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := hsplit

lemma lem_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
                                                                         
  have hstep := lem_zetaNsimplified2 s N hN
                                                       
  rw [lem_evalMainIntegral s hs N hN] at hstep

  have hden : (1 - s) ≠ 0 := by
    intro h
    have h1 : 1 = s := by simpa [sub_eq_zero] using h
    have h2 : s = 1 := h1.symm
    exact hs h2
  let A := (N : ℂ) ^ (1 - s)
                                                                             
  have h1 : (1 - s) * (A + s / (1 - s) * (A - 1)) = A - s := by
    calc
      (1 - s) * (A + s / (1 - s) * (A - 1))
          = (1 - s) * A + (1 - s) * (s / (1 - s) * (A - 1)) := by ring
      _ = (1 - s) * A + s * (A - 1) := by field_simp [hden]
      _ = A - s := by ring
  have h2 : (1 - s) * (A / (1 - s) + 1 + 1 / (s - 1)) = A - s := by
    have hne : s - 1 ≠ 0 := by simpa [sub_eq_zero] using hs
    field_simp [hden, hne]; ring
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) :=
    mul_left_cancel₀ hden (h1.trans h2.symm)

  rw [halg] at hstep
  exact hstep

lemma complex_tendsto_zero_iff_norm_tendsto_zero {α : Type*} {f : α → ℂ} {l : Filter α} :
    Tendsto f l (𝓝 0) ↔ Tendsto (fun x => ‖f x‖) l (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_zero_right]

lemma complex_norm_natCast_cpow (N : ℕ) (w : ℂ) (hN : 0 < N) :
    ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
  have hNnz : (N : ℂ) ≠ 0 := by
    simp [Ne, Nat.cast_eq_zero]
    exact ne_of_gt hN
  rw [Complex.norm_cpow_of_ne_zero hNnz]
  rw [Complex.norm_natCast]
  rw [Complex.natCast_arg]
  simp [Real.exp_zero]

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [complex_tendsto_zero_iff_norm_tendsto_zero]
                                
  have h1 : ∀ᶠ (N : ℕ) in atTop, ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact complex_norm_natCast_cpow N w hN
  rw [tendsto_congr' h1]

  have hw_pos : 0 < -w.re := neg_pos.mpr hw
                                 
  have h_eq : w.re = -(-w.re) := by ring
  rw [h_eq]
                                                                                               
  have h_comp : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h_rpow : Tendsto (fun x : ℝ => x ^ (-(-w.re))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hw_pos
  exact Tendsto.comp h_rpow h_comp

lemma lem_limitTerm1 (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_natCast_cpow_zero_of_neg_re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma lem_integrandBound (u : ℝ) (hu : 1 ≤ u) (s : ℂ) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                  
  set a : ℂ := ((Int.fract u : ℝ) : ℂ)
  set b : ℂ := (u : ℂ) ^ (-s - 1)
                  
  have hfract_le1 : ‖a‖ ≤ (1 : ℝ) := by
    simpa [a, Complex.norm_real] using (lem_fracPartBound u).2.2
                          
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
                                                     
  have h₁ : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by simp
  have h₂ : ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ :=
    mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
  have h₃ : ‖a * b‖ ≤ 1 * ‖b‖ := le_trans h₁ h₂
  have hle : ‖a * b‖ ≤ ‖b‖ := by simpa [one_mul] using h₃
                                                                   
  have hb : ‖b‖ = u ^ ((-s - 1).re) := by
    simpa [b] using
      Complex.norm_cpow_eq_rpow_re_of_pos (x := u) (hx := hu0) (y := -s - 1)
                                           
  have hexp : (-s - 1).re = -s.re - 1 := by
    simp [sub_eq_add_neg]
                                                       
  calc
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖
        = ‖a * b‖ := rfl
    _ ≤ ‖b‖ := hle
    _ = u ^ ((-s - 1).re) := hb
    _ = u ^ (-s.re - 1) := by simp [hexp]

lemma lem_integrandBoundeps (ε : ℝ) (_hε : 0 < ε) (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (hs : ε ≤ s.re) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
  have h1 : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := lem_integrandBound u hu s
  have h2 : -s.re - 1 ≤ -1 - ε := by linarith [hs]
  have h3 : u ^ (-s.re - 1) ≤ u ^ (-1 - ε) := Real.rpow_le_rpow_of_exponent_le hu h2
  exact le_trans h1 h3

lemma lem_triangleInequality_add (z₁ z₂ : ℂ) :
    ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  exact norm_add_le z₁ z₂

lemma lem_triangleInequality_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (_hf : IntervalIntegrable f volume a b) (h : a ≤ b) :
    ‖∫ u in a..b, f u‖ ≤ ∫ u in a..b, ‖f u‖ := by
                                                                                 
  simpa using (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) (a := a) (b := b) h)

lemma helper_integral_interval_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c : ℝ}
    (hab : IntervalIntegrable f volume a b) (hac : IntervalIntegrable f volume a c) :
    ((∫ x in a..b, f x) - ∫ x in a..c, f x) = ∫ x in c..b, f x := by
  simpa using
    (intervalIntegral.integral_interval_sub_left (μ := volume) (f := f) (a := a) (b := b) (c := c)
      hab hac)

lemma helper_integral_rpow_eval {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
                                         
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    have : ¬ m ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one hm)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by
    simpa [uIcc_of_le hmn] using h0notIcc
                              
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    have hplus := congrArg (fun t => t + 1) h
    have hminus : -ε = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hplus
    have hε0 : ε = 0 := by simpa using congrArg Neg.neg hminus
    exact (ne_of_gt hε) hε0
                                               
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    have hcond : (-1 < (-1 - ε)) ∨ ((-1 - ε) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc m n) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_rpow (a := m) (b := n) (r := -1 - ε) hcond)
                                                      
  have h1 : ((-1 - ε) + 1) = -ε := by
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
    simpa [h1]
      using hint
  have hnegnum : -(n ^ (-ε) - m ^ (-ε)) = m ^ (-ε) - n ^ (-ε) := by
    simp
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ (-ε) - m ^ (-ε)) / (-ε) := this
    _ = (n ^ (-ε) - m ^ (-ε)) * ((-ε)⁻¹) := by simp [div_eq_mul_inv]
    _ = (n ^ (-ε) - m ^ (-ε)) * (-(ε⁻¹)) := by simp [inv_neg]
    _ = -((n ^ (-ε) - m ^ (-ε)) * ε⁻¹) := by simp [mul_neg]
    _ = (-(n ^ (-ε) - m ^ (-ε))) * ε⁻¹ := by
      simpa using (neg_mul (n ^ (-ε) - m ^ (-ε)) (ε⁻¹)).symm
    _ = (m ^ (-ε) - n ^ (-ε)) * ε⁻¹ := by
      simp
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by simp [div_eq_mul_inv]

lemma helper_integral_rpow_le {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  have heval := helper_integral_rpow_eval (ε := ε) hε hm hmn
  have hn0 : 0 ≤ n := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans h01 (le_trans hm hmn)
  have hsub_le : m ^ (-ε) - n ^ (-ε) ≤ m ^ (-ε) := by
    exact sub_le_self _ (Real.rpow_nonneg hn0 (-ε))
  have hinv_nonneg : 0 ≤ ε⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hε)
  have hdiv_le : ((m ^ (-ε) - n ^ (-ε)) / ε) ≤ (m ^ (-ε) / ε) := by
    have := mul_le_mul_of_nonneg_right hsub_le hinv_nonneg
    simpa [div_eq_mul_inv, mul_comm] using this
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (m ^ (-ε) - n ^ (-ε)) / ε := heval
    _ ≤ m ^ (-ε) / ε := hdiv_le
    _ = (1 / ε) * m ^ (-ε) := by simp [div_eq_mul_inv, mul_comm]

lemma helper_tendsto_nat_rpow_neg (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun m : ℕ => (m : ℝ) ^ (-ε)) atTop (𝓝 0) := by
                                                                              
  have hcont : Tendsto (fun x : ℝ => x ^ (-ε)) atTop (𝓝 0) := by
                                                                              
    simpa using (tendsto_rpow_neg_atTop (y := ε) hε)

  have hcoe : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop

  have : Tendsto ((fun x : ℝ => x ^ (-ε)) ∘ fun n : ℕ => (n : ℝ)) atTop (𝓝 0) :=
    hcont.comp hcoe
                                       
  simpa using! this

lemma helper_exists_limit_of_tail_bound (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hb_nonneg : ∀ m, 0 ≤ b m)
    (hb_tendsto : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m) :
    ∃ l : ℂ, Tendsto a atTop (𝓝 l) := by
  classical
                                              
  have hCauchy : CauchySeq a := by
                                      
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
                                                               
    have h_ball : ∀ᶠ m in atTop, dist (b m) 0 < ε / 2 := by
      exact hb_tendsto (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
    have h_b_lt : ∀ᶠ m in atTop, b m < ε / 2 := by
      refine h_ball.mono ?_
      intro m hm
      have : |b m| < ε / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hm
      simpa [abs_of_nonneg (hb_nonneg m)] using this
                                  
    rcases eventually_atTop.1 hbound with ⟨M1, hM1⟩
    rcases eventually_atTop.1 h_b_lt with ⟨M2, hM2⟩
    let M := max M1 M2
    have hPM : ∀ᶠ n in atTop, M ≤ n → ‖a n - a M‖ ≤ b M := by
      have h' := hM1 M (le_max_left _ _)
      exact h'
    have hMb : b M < ε / 2 := hM2 M (le_max_right _ _)
    rcases eventually_atTop.1 hPM with ⟨N0, hN0⟩
    refine ⟨max N0 M, ?_⟩
    intro n hn k hk
    have hMn : M ≤ n := le_trans (le_max_right _ _) hn
    have hMk : M ≤ k := le_trans (le_max_right _ _) hk
    have hN0n : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hN0k : N0 ≤ k := le_trans (le_max_left _ _) hk
    have h1 : ‖a n - a M‖ ≤ b M := (hN0 n hN0n) hMn
    have h2 : ‖a k - a M‖ ≤ b M := (hN0 k hN0k) hMk
                                           
    have htri : ‖a n - a k‖ ≤ ‖a n - a M‖ + ‖a M - a k‖ := by
      have h := norm_add_le (a n - a M) (a M - a k)
      simpa [sub_add_sub_cancel (a n) (a M) (a k)] using h
    have h2' : ‖a M - a k‖ ≤ b M := by simpa [norm_sub_rev] using h2
    have hsumle : ‖a n - a k‖ ≤ b M + b M :=
      le_trans htri (add_le_add h1 h2')
    have hsumlt : b M + b M < ε := by
      have := add_lt_add hMb hMb
      simpa [add_halves] using this
    have : ‖a n - a k‖ < ε := lt_of_le_of_lt hsumle hsumlt
    simpa [dist_eq_norm] using this
                                                 
  rcases cauchySeq_tendsto_of_complete (u := a) hCauchy with ⟨l, hl⟩
  exact ⟨l, hl⟩

lemma helper_limit_norm_le_of_uniform_bound {a : ℕ → ℂ} {l : ℂ} {B : ℝ}
    (h : Tendsto a atTop (𝓝 l)) (hbound : ∀ n, ‖a n‖ ≤ B) : ‖l‖ ≤ B := by
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖l‖) := (Filter.Tendsto.norm h)
  exact le_of_tendsto' hnorm (fun n => by simpa using hbound n)

lemma helper_one_le_of_mem_Icc {m n u : ℝ} (hm : 1 ≤ m) (hu : u ∈ Icc m n) : 1 ≤ u := by
  exact le_trans hm hu.1

lemma helper_intervalIntegrable_rpow_neg {ε : ℝ} {a b : ℝ} (_hε : 0 < ε)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume a b := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc a b := by
    intro hx
    have : ¬ a ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one ha)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc a b := by
    simpa [uIcc_of_le hab] using h0notIcc
  simpa using
    (intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := a) (b := b) (r := -1 - ε)
      (Or.inr h0not))

lemma helper_one_le_of_mem_Ioc {m n u : ℝ} (hm : 1 ≤ m) (hu : u ∈ Ioc m n) : 1 ≤ u := by
  exact le_trans hm (le_of_lt hu.1)

lemma helper_integrableOn_of_bound_Ioc {m n : ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ}
  (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc m n)))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioc m n)), ‖f u‖ ≤ g u)
  (hg : IntegrableOn g (Ioc m n) volume) :
  IntegrableOn f (Ioc m n) volume := by
                                                                    
  let μ := volume.restrict (Ioc m n)
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by
    simp
                             
  have hg' : Integrable g μ := by
    simpa [μ] using! hg
                                           
  have hmeas' : AEStronglyMeasurable f μ := by
    simpa [μ] using hmeas
                                               
  have hineq : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
    simpa [μ, sub_eq_add_neg, norm_neg] using hbound
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas' hf0 hg' hineq
                                     
  simpa [μ] using! hf

lemma helper_aestronglyMeasurable_kernel_Ioc (s : ℂ) {m n : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Ioc m n)) := by
                                                           
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Ioc m n)) := by
    have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    have hmeas_coe : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
      (Complex.measurable_ofReal.comp hmeas_fract)
    exact hmeas_coe.aestronglyMeasurable
                                                        
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioc m n)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
      measurability
    exact hmeas.aestronglyMeasurable
                                             
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_aebound_kernel_Ioc {ε : ℝ} (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) (_hmn : m ≤ n) :
    ∀ᵐ u ∂(volume.restrict (Ioc m n)),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
                                                                                             
  refine
    ((ae_restrict_iff' (μ := volume) (s := Ioc m n)
        (p := fun u : ℝ => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε))
        measurableSet_Ioc)).2 ?_
                                                  
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu1 : 1 ≤ u := helper_one_le_of_mem_Ioc hm hu
  simpa using (lem_integrandBoundeps ε hε u hu1 s hs)

lemma helper_integrableOn_rpow_neg_Ioc {ε : ℝ} (hε : 0 < ε)
    {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntegrableOn (fun u : ℝ => u ^ (-1 - ε)) (Ioc m n) volume := by
  have hInt : IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume m n :=
    helper_intervalIntegrable_rpow_neg (ε := ε) hε hm hmn
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (f := fun u : ℝ => u ^ (-1 - ε)) hmn).1 hInt

lemma helper_intervalIntegrable_of_integrableOn_Ioc {f : ℝ → ℂ} {m n : ℝ}
  (hmn : m ≤ n) (hint : IntegrableOn f (Ioc m n) volume) :
  IntervalIntegrable f volume m n := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
    (a := m) (b := n) (f := f) hmn).2 hint

lemma helper_rpow_neg_nonneg_on {ε a b : ℝ} (_hε : 0 < ε) (ha : 1 ≤ a) (_hab : a ≤ b) :
    ∀ u ∈ Icc a b, 0 ≤ u ^ (-1 - ε) := by
  intro u hu
  have h1u : 1 ≤ u := le_trans ha hu.1
  have h0u : 0 ≤ u := le_trans (by norm_num) h1u
  exact Real.rpow_nonneg h0u (-1 - ε)

lemma helper_norm_integral_le_integral_norm_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ} (h : a ≤ b) :
  ‖∫ u in a..b, f u‖ ≤ ∫ u in a..b, ‖f u‖ := by
  simpa using (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) (a := a) (b := b) h)

lemma helper_tendsto_const_mul_zero (c : ℝ) {f : ℕ → ℝ}
  (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c * f n) atTop (𝓝 0) := by
  simpa using (Filter.Tendsto.const_mul (b := c) h)

lemma helper_limit_norm_le_of_eventual_bound {a : ℕ → ℂ} {l : ℂ} {B : ℝ}
  (h : Tendsto a atTop (𝓝 l)) (hbound : ∀ᶠ n in atTop, ‖a n‖ ≤ B) : ‖l‖ ≤ B := by
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖l‖) := (Filter.Tendsto.norm h)
  exact le_of_tendsto hnorm hbound

lemma lem_integralConvergence (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re) :
    ∃ I : ℂ,
      Tendsto
        (fun N : ℕ =>
          ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
        atTop (𝓝 I)
      ∧ ‖I‖ ≤ (1 / ε) := by
  classical
                
  let fC : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  let gR : ℝ → ℝ := fun u => u ^ (-1 - ε)
  let a : ℕ → ℂ := fun N => ∫ u in (1 : ℝ)..(N : ℝ), fC u
  let b : ℕ → ℝ := fun m => (1 / ε) * (m : ℝ) ^ (-ε)
          
  have hb_nonneg : ∀ m, 0 ≤ b m := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hpow : 0 ≤ (m : ℝ) ^ (-ε) := Real.rpow_nonneg hm0 _
    have hpos : 0 ≤ 1 / ε := by exact le_of_lt (one_div_pos.mpr hε)
    have := mul_le_mul_of_nonneg_left hpow hpos
    simpa [b] using this
          
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have hpow := helper_tendsto_nat_rpow_neg (ε := ε) hε
    have hmul := helper_tendsto_const_mul_zero (c := (1 / ε)) hpow
    simpa [b] using hmul
                                    
  have h_tail_pointwise : ∀ m n : ℕ, 1 ≤ m → m ≤ n → ‖a n - a m‖ ≤ b m := by
    intro m n hm1 hmn
                        
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
                                                                                     
    have hInt_f_1n : IntervalIntegrable fC volume (1 : ℝ) (n : ℝ) := by
                              
      have h1nNat : 1 ≤ n := le_trans hm1 hmn
      have h1nR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1nNat
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (n : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (n : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (hmn := h1nR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (_hmn := h1nR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (n : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (n : ℝ)) (f := fC) h1nR).2 hintOn
    have hInt_f_1m : IntervalIntegrable fC volume (1 : ℝ) (m : ℝ) := by
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (m : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (m : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (hmn := hmR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (_hmn := hmR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (m : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (m : ℝ)) (f := fC) hmR).2 hintOn
    have hdiff := helper_integral_interval_sub_left
      (E := ℂ) (f := fC) (a := (1 : ℝ)) (b := (n : ℝ)) (c := (m : ℝ))
      (hab := hInt_f_1n) (hac := hInt_f_1m)
    have hsub : a n - a m = ∫ u in (m : ℝ)..(n : ℝ), fC u := by
      simpa [a] using hdiff
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs
      (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (_hmn := hmnR)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (m : ℝ) (n : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (m : ℝ) (n : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_mn : IntervalIntegrable gR volume (m : ℝ) (n : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (m : ℝ)) (b := (n : ℝ)) (f := gR) hmnR).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR))
                                      
    have h1 : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ ∫ u in (m : ℝ)..(n : ℝ), gR u := by
      simpa using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (m : ℝ)) (b := (n : ℝ)) (f := fC) (g := gR)
          (hab := hmnR) (h := hbound_Ioc_imp) (hbound := hgInt_mn))
                                            
    have h3 : ∫ u in (m : ℝ)..(n : ℝ), gR u ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      helper_integral_rpow_le (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR)
              
    have : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      le_trans h1 h3
    simpa [hsub, b] using this
                        
  have hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m := by
    have h_m_ge1 : ∀ᶠ m in atTop, 1 ≤ m := eventually_ge_atTop 1
    refine h_m_ge1.mono ?_
    intro m hm1
    have h_n_ge_m : ∀ᶠ n in atTop, m ≤ n := eventually_ge_atTop m
    exact h_n_ge_m.mono (fun n hmn => by intro hle; exact h_tail_pointwise m n hm1 hle)
                           
  rcases helper_exists_limit_of_tail_bound a b hb_nonneg hb_tendsto hbound with ⟨I, hT⟩
                                    
  have h_eventual_bound : ∀ᶠ N in atTop, ‖a N‖ ≤ (1 / ε) := by
    have hN1 : ∀ᶠ N in atTop, 1 ≤ N := eventually_ge_atTop 1
    refine hN1.mono ?_
    intro N hNge1
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge1
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (_hmn := h1N)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (1 : ℝ) (N : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (1 : ℝ) (N : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_1N : IntervalIntegrable gR volume (1 : ℝ) (N : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (N : ℝ)) (f := gR) h1N).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N))
                                      
    have h1 : ‖∫ u in (1 : ℝ)..(N : ℝ), fC u‖ ≤ ∫ u in (1 : ℝ)..(N : ℝ), gR u := by
      simpa [a] using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (1 : ℝ)) (b := (N : ℝ)) (f := fC) (g := gR)
          (hab := h1N) (h := hbound_Ioc_imp) (hbound := hgInt_1N))
                                    
    have h3 : ∫ u in (1 : ℝ)..(N : ℝ), gR u ≤ (1 / ε) := by
      have := helper_integral_rpow_le (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N)
      simpa [one_div, Real.one_rpow, one_mul] using this
    have : ‖a N‖ ≤ (1 / ε) := by exact le_trans h1 h3
    exact this
                                              
  have hIle : ‖I‖ ≤ (1 / ε) :=
    helper_limit_norm_le_of_eventual_bound (a := a) (l := I) (B := 1 / ε) hT h_eventual_bound
                                                   
  refine ⟨I, ?_, hIle⟩
  simpa [a, fC] using hT

lemma helper_tendsto_zetaPartialSum_to_zeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  classical
                                                                                    
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
                          
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using (ne_of_gt this)
                                                          
  have hsum_div : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hgSumm : Summable g := by
    simpa [g, one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hsum_div
                                                   
  have h_eq_tail : (fun n => g (n + 1)) = h := by
    funext n; simp [g, h]
  have hhSumm : Summable h := by
    have : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [h_eq_tail] using this
                                                                         
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n : ℕ, h n) = ∑' n : ℕ, g n := by
    have hzero_add := (Summable.tsum_eq_zero_add (f := g) hgSumm)
                                                         
    have : (∑' n : ℕ, g n) = ∑' n : ℕ, g (n + 1) := by
      simpa [hg0, add_comm] using hzero_add
    simpa [h_eq_tail] using this.symm
                                             
  have hzeta : riemannZeta s = ∑' n : ℕ, g n := by
    simpa [g] using lem_zetaLimit s hs
                                                                         
  have h_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h n) atTop (𝓝 (∑' n, h n)) :=
    (Summable.tendsto_sum_tsum_nat hhSumm)
                                                               
  have htsumeq : (∑' n, h n) = riemannZeta s := h_tsum_eq.trans hzeta.symm
  simpa [zetaPartialSum, htsumeq, h] using h_tendsto

lemma integrableOn_of_ae_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {g : ℝ → ℝ} {s : Set ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict s))
    (hgint : IntegrableOn g s)
    (hbound : ∀ᵐ x ∂(volume.restrict s), ‖f x‖ ≤ g x) :
    IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := by
    simpa [IntegrableOn] using hgint
  have hf' : Integrable f (volume.restrict s) :=
    MeasureTheory.Integrable.mono' (μ := volume.restrict s) hg' hfm hbound
  simpa [IntegrableOn] using hf'

lemma kernel_aestronglyMeasurable_on_Ioi (s : ℂ) (a : ℝ) :
  AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioi a)) := by
                                                                                                           
  have hmeas_fract : Measurable (fun u : ℝ => (Int.fract u : ℝ)) := by
    simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have hmeas_fractC : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
    hmeas_fract.complex_ofReal
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
    have hmeas_ofReal : Measurable (fun u : ℝ => (u : ℂ)) := Complex.measurable_ofReal
    simpa using hmeas_ofReal.pow_const (-s - 1)
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) :=
    hmeas_fractC.mul hmeas_cpow
                                                                                                  
  simpa using hmeas.aestronglyMeasurable

lemma kernel_ae_bound_on_Ioi (s : ℂ) :
  ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                          
  let p : ℝ → Prop := fun u => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1)
                             
  have hAll : ∀ u ∈ Ioi (1 : ℝ), p u := by
    intro u hu
    have hu' : (1 : ℝ) ≤ u := le_of_lt hu
    dsimp [p]
    simpa using (lem_integrandBound u hu' s)
                                                          
  have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    MeasureTheory.ae_of_all _ hAll
                                                              
  have hiff :
      (∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)), p u) ↔ ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ)) (p := p)) measurableSet_Ioi
  exact hiff.mpr hAE

lemma helper_intervalIntegral_tendstoIoi_kernel (s : ℂ) (hs : 1 < s.re) :
  Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
    (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
                                                                    
  have hfm : AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi (1 : ℝ))) := by
    simpa using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
  have hbound' : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                                      
    simpa using kernel_ae_bound_on_Ioi (s := s)
  have hlt : (-s.re - 1) < (-1 : ℝ) := by linarith
  have hpos : 0 < (1 : ℝ) := by norm_num
  have hgint : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi (1 : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (a := (-s.re - 1)) (c := (1 : ℝ)) hlt hpos
  have hint : IntegrableOn (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
                              
    exact integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) hfm hgint hbound'
                                                   
  have hb : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (f := fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (a := (1 : ℝ))
      (b := fun N : ℕ => (N : ℝ)) hint hb)

lemma helper_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  simpa using (lem_zetaNfinal s hs N hN)

lemma helper_eventually_eq_from_zetaNfinal (s : ℂ) (hs : s ≠ 1) :
  ∀ᶠ N in atTop,
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hEv : ∀ᶠ N : ℕ in atTop, 1 ≤ N := Filter.eventually_ge_atTop (1 : ℕ)
  refine hEv.mono ?_
  intro N hN
  simpa using (helper_zetaNfinal s hs N hN)

lemma helper_limit_scaled_cpow (s : ℂ) (hs : 1 < s.re) (_hsne : s ≠ 1) :
  Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
  have h := lem_limitTerm1 s hs
  have h' := (Filter.Tendsto.const_mul (b := (1 / (1 - s))) h)
  simpa [div_eq_mul_inv, mul_comm] using h'

lemma helper_tendsto_const_mul {f : ℕ → ℂ} {l : ℂ} (c : ℂ)
  (h : Tendsto f atTop (𝓝 l)) : Tendsto (fun n => c * f n) atTop (𝓝 (c * l)) := by
  exact h.const_mul c

lemma helper_tendsto_add {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n + g n) atTop (𝓝 (a + b)) := by
                                                   
  have hpair : Tendsto (fun n => (f n, g n)) atTop (𝓝 (a, b)) := by
    simpa using (hf.prodMk_nhds hg)
  have hadd : Continuous (fun p : ℂ × ℂ => p.1 + p.2) := by
    simpa using! (continuous_fst.add continuous_snd)
  simpa using! ((hadd.tendsto (a, b)).comp hpair)

lemma helper_tendsto_neg {f : ℕ → ℂ} {a : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) : Tendsto (fun n => - f n) atTop (𝓝 (-a)) := by
  simpa only [Function.comp_def] using! ((continuous_neg.tendsto a).comp hf)

lemma helper_tendsto_sub {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n - g n) atTop (𝓝 (a - b)) := by
  have hneg : Tendsto (fun n => - g n) atTop (𝓝 (-b)) :=
    helper_tendsto_neg (f := g) (a := b) hg
  simpa [sub_eq_add_neg] using
    helper_tendsto_add (f := f) (g := fun n => - g n) hf hneg

lemma lem_zetaFormula (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s
      = 1 + 1 / (s - 1)
        - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  classical
                          
  have hsne : s ≠ 1 := by
    intro h
    have hlt : 1 < (1 : ℝ) := by simp [h, Complex.one_re] at hs
    exact (lt_irrefl _ ) hlt
                                                           
  let G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
                                          
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N := by
    simpa [G] using helper_eventually_eq_from_zetaNfinal s hsne
                                  
  have h_ps : Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) :=
    helper_tendsto_zetaPartialSum_to_zeta s hs
                                      
  have hG_to_zeta : Tendsto G atTop (𝓝 (riemannZeta s)) := by
    have hcongr := (Filter.tendsto_congr' (hl := hEv) :
      Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) ↔
      Tendsto G atTop (𝓝 (riemannZeta s)))
    exact hcongr.mp h_ps

  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) :=
    helper_limit_scaled_cpow s hs hsne
                                  
  have hK : Tendsto (fun _ : ℕ => (1 : ℂ) + 1 / (s - 1)) atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) :=
    tendsto_const_nhds
                                             
  have hInt : Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_intervalIntegral_tendstoIoi_kernel s hs
                           
  have hIntMul : Tendsto (fun N : ℕ => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_tendsto_const_mul (c := s) hInt
                                             
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 : ℂ) + 1 / (s - 1)
  have hA2 : Tendsto Aseq atTop (𝓝 0) := by simpa [Aseq] using hA
  have hK2 : Tendsto Kseq atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) := by simp [Kseq]
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (0 + ((1 : ℂ) + 1 / (s - 1)))) :=
    helper_tendsto_add (hf := hA2) (hg := hK2)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hIseq : Tendsto Iseq atTop (𝓝 (s * ∫ u in Ioi (1 : ℝ),
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
    simpa [Iseq] using hIntMul
  have hG_limit : Tendsto G atTop
      (𝓝 ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)))) := by
    have hSub := helper_tendsto_sub (hf := hSum) (hg := hIseq)
                                            
    have hGdef : (fun N => (Aseq N + Kseq N) - Iseq N) = G := by
      funext N; simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef]
      using hSub
                                                    
  have huniq :=
    tendsto_nhds_unique (f := G) (l := atTop)
      (a := riemannZeta s)
      (b := ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))))
      (ha := hG_to_zeta) (hb := hG_limit)
                                     
  simpa [zero_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using huniq

lemma lem_zetaanalOnnot1 : AnalyticOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
                                                                             
  have hset : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext z; simp
  have hopen : IsOpen ({s : ℂ | s ≠ 1}) := by
    simp [hset]
                                               
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
    intro z hz

    simpa using (differentiableAt_riemannZeta (by simpa [Set.mem_ofPred_eq] using hz)).differentiableWithinAt
  simpa [Complex.analyticOn_iff_differentiableOn hopen] using hdiff

lemma lem_zetaanalS : (let S := {s : ℂ | s ≠ 1}; AnalyticOn ℂ riemannZeta S) := by exact lem_zetaanalOnnot1

lemma lem_S_isOpen : (let S := {s : ℂ | s ≠ 1}; IsOpen S) := by
                                                            
  have h : {s : ℂ | s ≠ 1} = {(1 : ℂ)}ᶜ := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h]
  exact isOpen_compl_singleton

lemma lem_T_isOpen : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsOpen T) := by
                                      
  show IsOpen {s : ℂ | s ≠ 1 ∧ 1/10 < s.re}

  apply IsOpen.and
  ·                           
    exact lem_S_isOpen
  ·                                 
                                                             
    have h_eq : {s : ℂ | 1/10 < s.re} = Complex.re ⁻¹' (Set.Ioi (1/10)) := by
      ext s
      simp [Set.mem_preimage, Set.mem_Ioi]
    rw [h_eq]
    exact Complex.continuous_re.isOpen_preimage (Set.Ioi (1/10)) isOpen_Ioi

lemma helper_T_open : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsOpen T) := by
  classical
                                           
  intro S T
                               
  have hSopen : IsOpen S := by simpa using lem_S_isOpen
                                                                                                 
  have hHalfplane : IsOpen {s : ℂ | (1 / 10 : ℝ) < s.re} := by
    have : IsOpen ((fun s : ℂ => s.re) ⁻¹' Ioi (1 / 10 : ℝ)) :=
      IsOpen.preimage (hf := Complex.continuous_re) (t := Ioi (1 / 10 : ℝ)) (h := isOpen_Ioi)
    simpa [Set.preimage, Ioi] using this
                                        
  have hInter : IsOpen (S ∩ {s : ℂ | (1 / 10 : ℝ) < s.re}) := hSopen.inter hHalfplane
                                       
  simpa [T, Set.ofPred_and] using hInter

lemma open_mem_interior_of_isOpen {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) : x ∈ interior U := by simpa [hU.interior_eq] using hx

lemma isOpen_halfplane_re_gt (a : ℝ) : IsOpen {z : ℂ | a < z.re} := by
  simpa [Set.mem_ofPred_eq] using
    (isOpen_lt (hf := continuous_const) (hg := Complex.continuous_re))

lemma T_eq_inter_S_half (S T : Set ℂ) (_hS : S = {s : ℂ | s ≠ 1}) (hT : T = {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}) :
  T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
  classical
  ext z
  simp [hT, Set.inter_def]

lemma inter_compl_singleton_eq_diff {α : Type*} [DecidableEq α] (A : Set α) (x : α) :
  A ∩ ({x} : Set α)ᶜ = A \ ({x} : Set α) := by
  ext z; simp [Set.mem_inter_iff, Set.mem_singleton_iff]

lemma joinedIn_of_path_forall_mem {s : Set ℂ} {x y : ℂ}
  (γ : Path x y) (hγ : ∀ t, γ t ∈ s) : JoinedIn s x y := by
  exact ⟨γ, hγ⟩

lemma path_forall_mem_symm {x y : ℂ} {P : ℂ → Prop} (γ : Path x y)
  (h : ∀ t, P (γ t)) : ∀ t, P (γ.symm t) := by
  intro t
  simpa [Path.symm] using (h (unitInterval.symm t))

lemma isPathConnected_punctured_halfplane_re_gt (a : ℝ) (p : ℂ) (hp : a < p.re) :
  IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
                                                                 
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
                            
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
                    
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
                           
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
                          
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
                               
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    ·         
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    ·         
      simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    ·         
      simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    ·         
      simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
                      
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    ·               
      refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    ·               
      refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
                                      
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
                                                 
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
                            
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      ·                        
        exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      ·                                             
        rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        ·                    
          exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        ·                                                
          have hz_eq : z = p := by
                                              
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by
              simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by
              simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
                                            
              simp [heq, himeq]
                                
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        ·                    
          exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      ·                         
        exact Or.inr (Or.inr hgt)
    · intro hz
                        
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          ·             
            intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          ·             
            intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
             
  simpa [hcover] using hUnionPC

lemma inter_compl_singleton_eq_diff' {α : Type*} [DecidableEq α] (A : Set α) (x : α) :
  A ∩ ({x} : Set α)ᶜ = A \ ({x} : Set α) := by
  ext z; simp [Set.mem_inter_iff, Set.mem_singleton_iff]

lemma lem_T_isPreconnected : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsPreconnected T) := by
  classical
                              
  let S : Set ℂ := {s : ℂ | s ≠ 1}
  let T : Set ℂ := {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}
                                 
  have hTinter : T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
    simpa using (T_eq_inter_S_half S T (by rfl) (by rfl))
                                       
  have hScompl : S = ({(1 : ℂ)} : Set ℂ)ᶜ := by
    ext z; simp [S]
                                            
  have hTdiff : T = {s : ℂ | (1/10 : ℝ) < s.re} \ (({(1 : ℂ)} : Set ℂ)) := by
    have : T = {s : ℂ | (1/10 : ℝ) < s.re} ∩ S := by
      simpa [Set.inter_comm] using hTinter
                                                                    
    simpa [hScompl, inter_compl_singleton_eq_diff] using this
                     
  have hp : (1/10 : ℝ) < (1 : ℂ).re := by
    simpa using (by norm_num : (1/10 : ℝ) < (1 : ℝ))
                                               
  have hpc : IsPathConnected ({z : ℂ | (1/10 : ℝ) < z.re} \ (({(1 : ℂ)} : Set ℂ))) :=
    isPathConnected_punctured_halfplane_re_gt (a := (1/10 : ℝ)) (p := (1 : ℂ)) (hp := hp)
                                              
  have hpcT : IsPathConnected T := by
    simpa [hTdiff] using hpc
                                                         
  have hconnT : IsConnected T := hpcT.isConnected
  exact (IsConnected.isPreconnected (s := T) hconnT)

lemma hasDerivAt_param_cpow_neg_one (u : ℝ) (hu : 0 < u) (z : ℂ) :
  HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1)) (-(Real.log u) * (u : ℂ) ^ (-z - 1)) z := by
                                         
  have hcu : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
                                           
  have hId : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := by simpa using! (hasDerivAt_id (x := z))
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) z := by simpa using! hId.neg
  have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1 : ℂ) z := by
                          
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg.add_const (-1 : ℂ)
                                                                  
  have h := (HasDerivAt.const_cpow (c := (u : ℂ)) (hf := hf) (h0 := Or.inl hcu))
                                                                          
  have clog : Complex.log (u : ℂ) = (Real.log u : ℂ) := by
    simpa using (Complex.ofReal_log (x := u) (hx := le_of_lt hu)).symm
  simpa [clog, mul_comm, mul_left_comm, mul_assoc] using h

lemma integrableOn_t_mul_exp_neg (ε : ℝ) (hε : 0 < ε) : IntegrableOn (fun t : ℝ => t * Real.exp (- ε * t)) (Ioi (0 : ℝ)) := by
                                                                       
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ)) (b := ε)
    (hs := by norm_num) (hp := by norm_num) (hb := hε)
                      
  simpa [Real.rpow_one] using h

lemma aestronglyMeasurable_kernel_param_deriv (z : ℂ) :
  AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
                                                                  
  let μ := volume.restrict (Ioi (1 : ℝ))
                                                                                                 
  have hmeas_logR : Measurable (fun u : ℝ => Real.log u) := Real.measurable_log
  have hmeas_logC : Measurable (fun u : ℝ => ((Real.log u) : ℂ)) := hmeas_logR.complex_ofReal
  have hmeas_neg : Measurable (fun u : ℝ => -((Real.log u) : ℂ)) := hmeas_logC.neg
  have h1 : AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ)) μ := by
    simpa [μ] using hmeas_neg.aestronglyMeasurable
                                                                                 
  have h2 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) μ := by
    simpa [μ] using kernel_aestronglyMeasurable_on_Ioi (s := z) (a := (1 : ℝ))
                                      
  have hmul : AEStronglyMeasurable
      (fun u : ℝ => (-((Real.log u) : ℂ)) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)))
      μ := (MeasureTheory.AEStronglyMeasurable.mul h1 h2)
  simpa [μ] using hmul

lemma kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
  ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖ ≤ Real.log u * u ^ (-1 - ε) := by
                                       
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
                                                                  
  have hinner1 : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-x.re - 1) := by
    simpa using (lem_integrandBound u hu1 x)
  have hexp_le : -x.re - 1 ≤ -1 - ε := by linarith
  have hmono : u ^ (-x.re - 1) ≤ u ^ (-1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hu1 hexp_le
  have hinner : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-1 - ε) :=
    le_trans hinner1 hmono
                      
  have hmul : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
      = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := by
    simp
  have hnorm_nonneg : 0 ≤ ‖-((Real.log u) : ℂ)‖ := by simp
  have hmul_le : ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖
      ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := by
    exact mul_le_mul_of_nonneg_left hinner hnorm_nonneg
                                                                  
  have hlognorm_neg : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
             
  calc
    ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
        = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := hmul
    _ ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := hmul_le
    _ = (Real.log u) * u ^ (-1 - ε) := by simp [hlognorm_neg, mul_comm]

lemma exists_radius_ball_two_step_subset_halfspace (s : ℂ) {ε : ℝ} (hε : ε < s.re) :
  ∃ δ > 0, ∀ x, dist x s < δ → ∀ y, dist y x < δ → ε ≤ y.re := by
                                  
  set δ : ℝ := (s.re - ε) / 2 with hδdef
  have hpos : 0 < s.re - ε := sub_pos.mpr hε
  have hδpos : 0 < δ := by simpa [hδdef] using (half_pos hpos)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy
                                                                           
  have htri : dist y s ≤ dist y x + dist x s := by
    simpa using (dist_triangle y x s)
  have hsumlt : dist y x + dist x s < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - s‖ < δ + δ := by
    have := lt_of_le_of_lt htri hsumlt
    simpa [dist_eq_norm] using this
  have hdeltaSum : δ + δ = s.re - ε := by
    simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - s‖ < s.re - ε := by simpa [hdeltaSum] using hnorm_lt
                                  
  have h_eps_lt : ε < s.re - ‖y - s‖ := by
    have hsum' : ε + ‖y - s‖ < s.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_right hnorm_lt_re ε)
    simpa [lt_sub_iff_add_lt] using hsum'
                                       
  have hre_abs : |(y - s).re| ≤ ‖y - s‖ := by
    simpa using (Complex.abs_re_le_norm (y - s))
  have hre_lower : -‖y - s‖ ≤ (y - s).re := by
                                                  
    have hpair := (abs_le.mp hre_abs)
    exact hpair.left
  have hyge : s.re - ‖y - s‖ ≤ y.re := by
    have h' : s.re + (-‖y - s‖) ≤ s.re + (y - s).re := add_le_add_right hre_lower s.re
    have h'' : s.re + (y - s).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
                                            
  have hygt : ε < y.re := lt_of_lt_of_le h_eps_lt hyge
  exact le_of_lt hygt

lemma integrable_kernel_at_param (s : ℂ) (hs : 0 < s.re) :
  Integrable ((fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
  classical
                                                
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set ε : ℝ := s.re / 2
  set g1 : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
                                           
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [f] using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
                       
  have hε : 0 < ε := by
    have : 0 < s.re := hs
    simpa [ε] using (half_pos this)
  have hεle : ε ≤ s.re := by
    have hnonneg : 0 ≤ s.re := le_of_lt hs
    simpa [ε] using (half_le_self hnonneg)
                                            
  have hbound1 : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g1 u := by
    simpa [f, g1] using (kernel_ae_bound_on_Ioi (s := s))
                                             
  have hpow_ae : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), g1 u ≤ g u := by
                                      
    have hAll : ∀ u ∈ Ioi (1 : ℝ), g1 u ≤ g u := by
      intro u hu
      have hx : (1 : ℝ) ≤ u := le_of_lt hu
      have hlexp : (-s.re - 1) ≤ (-1 - ε) := by linarith
      have := Real.rpow_le_rpow_of_exponent_le hx hlexp
      simpa [g1, g] using this
                                           
    have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → g1 u ≤ g u :=
      MeasureTheory.ae_of_all _ hAll
    have hiff :=
      (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ))
        (p := fun u => g1 u ≤ g u) measurableSet_Ioi)
    exact hiff.mpr hAE
                   
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g u := by
    filter_upwards [hbound1, hpow_ae] with u hu1 hu2
    exact le_trans hu1 hu2
                                               
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    have ha_lt : (-1 - ε) < (-1 : ℝ) := by linarith
    have hc : 0 < (1 : ℝ) := by norm_num
    simpa [g] using (integrableOn_Ioi_rpow_of_lt (a := (-1 - ε)) (ha := ha_lt) (c := (1 : ℝ)) (hc := hc))
                                        
  have hint : IntegrableOn f (Ioi (1 : ℝ)) :=
    integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) (f := f) (g := g)
      (hfm := hfm) (hgint := hgint) (hbound := hbound)
  simpa [IntegrableOn, f] using hint

lemma eventually_aestronglyMeasurable_kernel_param (s : ℂ) :
  ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) (volume.restrict (Ioi (1 : ℝ))) := by
  refine Filter.Eventually.of_forall ?_
  intro z
                                
  have hmeas_fract : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) := by
    have hmeas_fr : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    exact (Complex.measurable_ofReal.comp hmeas_fr)
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-z - 1)) := by
                                                                                
    measurability
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) :=
    hmeas_fract.mul hmeas_cpow
  simpa using hmeas.aestronglyMeasurable

lemma hasDerivAt_kernel_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
  HasDerivAt (fun w : ℂ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))
    ( -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) ) z := by
                       
  set c0 : ℂ := ((Int.fract u : ℝ) : ℂ)
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu0
  have hcz : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
                                      
  have hfneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfneg.sub_const (1 : ℂ)
                                         
  have hbase : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) (hf := hf) (h0 := Or.inl hcz)
  have hbase' : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
                        
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
                            
  have hmul : HasDerivAt (fun w : ℂ => c0 * ((u : ℂ) ^ (-w - 1)))
      (c0 * (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1))) z :=
    HasDerivAt.const_mul c0 hbase'
                                             
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (Complex.ofReal_log (x := u) (hx := le_of_lt hu0))
                        
  simpa [c0, hlog, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ)
  (hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, HasDerivAt (fun w => F w u) (F' z u) z)
  :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
                                                                                                 
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (hs := Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint)
      (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int)
      (h_diff := hderiv)
  rcases h with ⟨_hint, hDeriv⟩
                                                                                 
  simpa using hDeriv

lemma dist_lt_of_mem_two_balls {x z s : ℂ} {r : ℝ}
  (hxz : dist x z < r) (hzs : dist z s < r) : dist x s < r + r := by
  have htri : dist x s ≤ dist x z + dist z s := dist_triangle x z s
  have hadd : dist x z + dist z s < r + r := add_lt_add hxz hzs
  exact lt_of_le_of_lt htri hadd

lemma mem_ball_of_mem_two_half_balls {x z s : ℂ} {δ : ℝ}
  (hx : x ∈ Metric.ball z (δ/2)) (hz : z ∈ Metric.ball s (δ/2)) :
  x ∈ Metric.ball s δ := by
  have hxz : dist x z < δ / 2 := by
    simpa [Metric.mem_ball] using hx
  have hzs : dist z s < δ / 2 := by
    simpa [Metric.mem_ball] using hz
  have htri : dist x s ≤ dist x z + dist z s := dist_triangle x z s
  have hadd : dist x z + dist z s < δ / 2 + δ / 2 := add_lt_add hxz hzs
  have hlt : dist x s < δ := by
    exact lt_of_le_of_lt htri (by simpa [add_halves] using hadd)
  simpa [Metric.mem_ball] using hlt

lemma dist_lt_delta_of_half {x s : ℂ} {δ : ℝ} (hδpos : 0 < δ)
  (hx : dist x s < δ/2) : dist x s < δ := by
  have hhalf : δ / 2 < δ := by
    simpa using (half_lt_self hδpos)
  exact lt_trans hx hhalf

lemma re_lower_bound_from_two_step {s x : ℂ} {ε δ : ℝ}
  (h : ∀ z, dist z s < δ → ∀ y, dist y z < δ → ε ≤ y.re)
  (hδpos : 0 < δ) (hx : dist x s < δ) : ε ≤ x.re := by
  have hxx : dist x x < δ := by simpa [dist_self] using hδpos
  have hxstep := h x hx
  have hxres := hxstep x hxx
  simpa using hxres

lemma analyticAt_of_eventually_differentiableAt {f : ℂ → ℂ} {s : ℂ}
  (h : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ f z) : AnalyticAt ℂ f s := by
  simpa using
    (Complex.analyticAt_iff_eventually_differentiableAt (f := f) (c := s)).2 h

lemma kernel_integrable_param_of_re_pos (z : ℂ) (hz : 0 < z.re) :
  Integrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))
    (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
  simpa using (integrable_kernel_at_param (s := z) (hs := hz))

lemma integrable_kernel_at_param' (z : ℂ) (hz : 0 < z.re) :
  Integrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))
    (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by simpa using integrable_kernel_at_param (s := z) hz

lemma lem_integralAnalytic (s : ℂ) (hs : 1/10 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
  classical
                                                            
  have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1/10) hs
  set ε : ℝ := s.re / 2 with hεdef
  have hεpos : 0 < ε := by simpa [ε] using (half_pos hspos)
  have hεlt : ε < s.re := by
    have : s.re / 2 < s.re := by simpa [ε] using (half_lt_self hspos)
    simpa [ε] using this
                                                                        
  rcases exists_radius_ball_two_step_subset_halfspace (s := s) (ε := ε) hεlt with ⟨δ, hδpos, hδprop⟩
                                                            
  let F : ℂ → ℝ → ℂ := fun z u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)
  let F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
                                                 
  let bound : ℝ → ℝ := fun u => (2/ε) * u ^ (-1 - (ε/2))
                                                     
  have hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have hlt : (-1 - (ε/2)) < (-1 : ℝ) := by
      have : 0 < ε/2 := by simpa using (half_pos hεpos)
      linarith
    have hpos1 : 0 < (1 : ℝ) := by norm_num
    have hpow_int : IntegrableOn (fun u : ℝ => u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) := by
      simpa using (integrableOn_Ioi_rpow_of_lt (a := (-1 - (ε/2))) hlt (c := (1 : ℝ)) hpos1)
    have hconst : IntegrableOn (fun u : ℝ => (2/ε) * u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) :=
      hpow_int.const_mul (2/ε)
    simpa [IntegrableOn, bound] using hconst
                                                                                  
  have hDiff_eventually : ∀ᶠ z in 𝓝 s,
      DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
                                              
    have hball : Metric.ball s (δ/2) ∈ 𝓝 s := Metric.ball_mem_nhds _ (by simpa using (half_pos hδpos))
    refine Filter.eventually_of_mem hball ?_
    intro z hz
                                                                                            
    have hz_lt_δ : dist z s < δ := lt_trans (by simpa [Metric.mem_ball] using hz) (by simpa using (half_lt_self hδpos))
    have hRe_inner : ∀ y, y ∈ Metric.ball z (δ/2) → ε ≤ y.re := by
      intro y hy
      have hy_lt_δ : dist y z < δ := lt_trans (by simpa [Metric.mem_ball] using hy) (by simpa using (half_lt_self hδpos))
      exact hδprop z hz_lt_δ y hy_lt_δ
                                              
    have hmeas_z : ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable (F w) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
      eventually_aestronglyMeasurable_kernel_param (s := z)
                                                                     
    have hzRe_ge : ε ≤ z.re := by
                                                      
      have hss : dist s s < δ := by simpa [dist_self] using hδpos
      have hz_lt_δ' : dist z s < δ := hz_lt_δ
      exact hδprop s hss z hz_lt_δ'
    have hzpos : 0 < z.re := lt_of_lt_of_le hεpos hzRe_ge
    have hFint_z : Integrable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F] using integrable_kernel_at_param (s := z) hzpos
                                      
    have hF'meas_z : AEStronglyMeasurable (F' z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F, F'] using aestronglyMeasurable_kernel_param_deriv (z := z)
                                                       
    have hbound_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
                                                                                           
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
        intro u hu w hw
        have hu1 : 1 < u := hu
        have hu0 : 0 < u := lt_trans zero_lt_one hu1
                                                             
        have hwRe : ε ≤ w.re := hRe_inner w hw
        have hker : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))‖
              ≤ Real.log u * u ^ (-1 - ε) :=
          kernel_deriv_norm_bound_on_ball (ε := ε) (u := u) (hu := hu1) (x := w) (hx := hwRe)
        have hF'le : ‖F' w u‖ ≤ Real.log u * u ^ (-1 - ε) := by
          simpa [F, F', mul_comm, mul_left_comm, mul_assoc] using hker
                                                    
        have hx' := Real.add_one_le_exp ((ε/2) * Real.log u)
        have hx : 1 + (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          simpa [add_comm] using hx'
        have hsub : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) - 1 := by
          have := sub_le_sub_right hx 1
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hle_exp : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          have hnonneg : 0 ≤ (1 : ℝ) := by norm_num
          have : Real.exp ((ε/2) * Real.log u) - 1 ≤ Real.exp ((ε/2) * Real.log u) :=
            sub_le_self _ hnonneg
          exact le_trans hsub this
        have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
        have hpos_inv : 0 < ε⁻¹ := inv_pos.mpr hεpos
        have hpos_coeff : 0 < (2/ε) := by
          have : 0 < (2 : ℝ) := by norm_num
          simpa [one_div, div_eq_mul_inv] using (mul_pos this hpos_inv)
        have hlog_bound : Real.log u ≤ (2/ε) * Real.exp ((ε/2) * Real.log u) := by
          have hmul := mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
                                            
          have hleft : (2/ε) * ((ε/2) * Real.log u) = Real.log u := by
            have h2ne : (2 : ℝ) ≠ 0 := by norm_num
            calc
              (2/ε) * ((ε/2) * Real.log u)
                  = ((2/ε) * (ε/2)) * Real.log u := by ring
              _ = ((2 * ε⁻¹) * (ε * (2)⁻¹)) * Real.log u := by simp [div_eq_mul_inv]
              _ = ((2 * (2)⁻¹) * (ε⁻¹ * ε)) * Real.log u := by ring
              _ = (1 * 1) * Real.log u := by simp [hεne, h2ne]
              _ = Real.log u := by simp
          simpa [hleft]
            using hmul
                                                
        have hexp_rpow : Real.exp ((ε/2) * Real.log u) = u ^ (ε/2) := by
          have : 0 < u := hu0
          simp [Real.rpow_def_of_pos this, mul_comm]
                                                 
        have hmul : Real.log u * u ^ (-1 - ε)
              ≤ ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) := by
          have hqpos : 0 < u ^ (-1 - ε) := Real.rpow_pos_of_pos hu0 _
          have hq : 0 ≤ u ^ (-1 - ε) := le_of_lt hqpos
          exact mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound) hq
                                                                    
        have hpow_mul : u ^ (ε/2) * u ^ (-1 - ε) = u ^ (-1 - (ε/2)) := by
          have hu0' : 0 < u := hu0
          have h1 : Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u)
              = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
            simpa using (Real.exp_add ((ε/2) * Real.log u) ((-1 - ε) * Real.log u)).symm
          calc
            u ^ (ε/2) * u ^ (-1 - ε)
                = Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u) := by
                    simp [Real.rpow_def_of_pos hu0', mul_comm]
            _ = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
                    simpa using h1
            _ = Real.exp (((ε/2) + (-1 - ε)) * Real.log u) := by
                    ring_nf
            _ = u ^ (-1 - (ε/2)) := by
                    have : (ε/2) + (-1 - ε) = -1 - (ε/2) := by ring
                    simp [this, Real.rpow_def_of_pos hu0', mul_comm]
        have hmul' : ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) = (2/ε) * u ^ (-1 - (ε/2)) := by
          simp [mul_assoc, hpow_mul]
                      
        have : ‖F' w u‖ ≤ bound u := by
          refine le_trans hF'le ?_
          simpa [bound, hmul'] using hmul
        simpa [F, F', bound]
          using this
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                           
    have hderiv_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
                                                  
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2),
          HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
        intro u hu w hw
        simpa [F, F', mul_comm, mul_left_comm, mul_assoc]
          using hasDerivAt_kernel_in_param (u := u) (hu := hu) (z := w)
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2),
            HasDerivAt (fun w0 => F w0 u) (F' w u) w) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                         
    have hD := hasDerivAt_integral_param_dominated_Ioi
      (F := F) (F' := F') (s := z) (δ := δ/2) (hδ := by simpa using (half_pos hδpos))
      (hmeas := hmeas_z) (hFint := hFint_z) (hF'meas := hF'meas_z)
      (bound := bound) (hbound_int := hbound_int) (hbound := hbound_z) (hderiv := hderiv_z)
                                      
    simpa using hD.differentiableAt
                                                               
  exact analyticAt_of_eventually_differentiableAt hDiff_eventually

lemma lem_zetaFormulaAC :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     let F := fun z : ℂ =>
       z / (z - 1)
       - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)
     AnalyticOn ℂ F T) := by
                                    
  simp only [AnalyticOn]
  intro s hs
  simp at hs
  obtain ⟨hs_ne_1, hs_re⟩ := hs

  apply AnalyticAt.analyticWithinAt

  have h1 : AnalyticAt ℂ (fun z => z / (z - 1)) s := by
    apply AnalyticAt.div
    · exact analyticAt_id
    · exact analyticAt_id.sub analyticAt_const
    ·                             
      rw [sub_ne_zero]
      exact hs_ne_1

  have hs_re_eq : (10 : ℝ)⁻¹ = (1 : ℝ) / 10 := by norm_num
  have hs_re_correct : (1 : ℝ) / 10 < s.re := by rwa [← hs_re_eq]

  have hconv := lem_integralConvergence (1/10) (by norm_num) s (le_of_lt hs_re_correct)

  obtain ⟨I, hI_tendsto, hI_bound⟩ := hconv

  have hI_bound_10 : ‖I‖ ≤ 10 := by
    convert hI_bound
    norm_num

  have h_integral : AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    apply lem_integralAnalytic s hs_re_correct

  have h2 : AnalyticAt ℂ (fun z => z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    exact analyticAt_id.mul h_integral

  exact h1.sub h2

lemma lem_div_eq_one_plus_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + 1 / (z - 1) := by
  have h : z - 1 ≠ 0 := by
    intro h0
    have : z = 1 := by
      rw [sub_eq_zero] at h0
      exact h0
    exact hz this
  calc z / (z - 1)
    = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + 1 / (z - 1) := by simp [div_self h]

lemma lem_zetaAnalyticContinuation :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     ∀ s ∈ T,
       riemannZeta s
         = 1 + 1 / (s - 1)
           - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
                              
  simp only [Set.mem_ofPred_eq]
  intro s h_s
                          
  have hs_ne_1 : s ≠ 1 := h_s.1
  have hs_re : 1/10 < s.re := h_s.2

  let F := fun z : ℂ => 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)

  let S := {s : ℂ | s ≠ 1}
  let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}

  have hs_in_T : s ∈ T := by
    simp only [T, S, Set.mem_ofPred_eq]
    exact ⟨hs_ne_1, hs_re⟩

  have h_T_open := lem_T_isOpen
  have h_T_preconnected := lem_T_isPreconnected

  have h_zeta_analytic_S := lem_zetaanalS
  have h_zeta_analytic_T : AnalyticOn ℂ riemannZeta T := by
    apply AnalyticOn.mono h_zeta_analytic_S
    intro x hx; exact hx.1
  have h_zeta_analyticOnNhd_T : AnalyticOnNhd ℂ riemannZeta T := by
    rwa [← h_T_open.analyticOn_iff_analyticOnNhd]

  have h_F_orig_analytic := lem_zetaFormulaAC
                                                                                 
  have h_F_eq : EqOn F (fun z => z / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) T := by
    intro z hz
    simp only [F]
    rw [lem_div_eq_one_plus_one_div z hz.1]

  have h_F_analytic_T : AnalyticOn ℂ F T :=
    AnalyticOn.congr h_F_orig_analytic h_F_eq
  have h_F_analyticOnNhd_T : AnalyticOnNhd ℂ F T := by
    rwa [← h_T_open.analyticOn_iff_analyticOnNhd]

  have ⟨s₀, hs₀_T, hs₀_re⟩ : ∃ s₀, s₀ ∈ T ∧ 1 < s₀.re := by
    use 2
    constructor
    · simp only [T, S, Set.mem_ofPred_eq]
      norm_num
    · norm_num

  have h_eventually_eq : riemannZeta =ᶠ[𝓝 s₀] F := by
                                                                                 
    have h_re_cont : ContinuousAt Complex.re s₀ := Complex.continuous_re.continuousAt
    have h_nhd_re : ∀ᶠ s in 𝓝 s₀, 1 < s.re :=
      ContinuousAt.eventually_lt continuousAt_const h_re_cont hs₀_re
                                            
    have h_nhd_T : ∀ᶠ s in 𝓝 s₀, s ∈ T := h_T_open.mem_nhds hs₀_T

    filter_upwards [h_nhd_re, h_nhd_T] with w hw_re hw_T
                                            
    have h_formula := lem_zetaFormula w hw_re
    simp only [F]
    exact h_formula

  have h_eqOn_global := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    h_zeta_analyticOnNhd_T h_F_analyticOnNhd_T h_T_preconnected hs₀_T h_eventually_eq

  exact h_eqOn_global hs_in_T

lemma lem_zetaBound1 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ := by
  classical
  set S : Set ℂ := {z : ℂ | z ≠ 1}
  set T : Set ℂ := {z : ℂ | z ∈ S ∧ 1/10 < z.re}
  set Iint : ℂ := ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hT : s ∈ T := by
    have hsS : s ∈ S := by simpa [S, Set.mem_ofPred_eq] using hs_ne
    simpa [T, Set.mem_ofPred_eq] using And.intro hsS hs_re
  have hAC : ∀ z ∈ T, riemannZeta z = 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1) := by
    simpa [S, T] using lem_zetaAnalyticContinuation
  have hzeta : riemannZeta s = 1 + 1 / (s - 1) - s * Iint := by
    simpa [Iint] using hAC s hT
  have h1 : ‖riemannZeta s‖ ≤ ‖1 + 1 / (s - 1)‖ + ‖-s * Iint‖ := by
    simpa [hzeta, sub_eq_add_neg] using (lem_triangleInequality_add (1 + 1 / (s - 1)) (-s * Iint))
  have hA : ‖1 + 1 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖1 / (s - 1)‖ := by
    simpa using (lem_triangleInequality_add (1 : ℂ) (1 / (s - 1)))
  have hmul : ‖-s * Iint‖ = ‖-s‖ * ‖Iint‖ := by
    simp
  have hB : ‖-s * Iint‖ ≤ ‖s‖ * ‖Iint‖ := by
    have : ‖-s * Iint‖ = ‖s‖ * ‖Iint‖ := by simp
    exact this.le
  have h2 : ‖riemannZeta s‖ ≤ (‖(1 : ℂ)‖ + ‖1 / (s - 1)‖) + (‖s‖ * ‖Iint‖) :=
    le_trans h1 (add_le_add hA hB)
  have h1norm : ‖(1 : ℂ)‖ = 1 := by simp
  simpa [Iint, h1norm, add_comm, add_left_comm, add_assoc] using h2

lemma lem_integralBoundValue (s : ℂ) (hs : 0 < s.re) : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := by exact zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp

lemma lem_zetaBound2 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
                                            
  set f : ℝ → ℂ := fun u => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) with hfdef
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1) with hgdef
                               
  have hζ : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ := by
    simpa [hfdef] using lem_zetaBound1 s hs_re hs_ne
                                               
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
                                   
  have h_ae_bound : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
    have hforall : ∀ u ∈ Ioi (1 : ℝ), ‖f u‖ ≤ g u := by
      intro u hu
      have := lem_integrandBound u (le_of_lt hu) s
      simpa [hfdef, hgdef] using this
    have hmeas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
    simpa [μ] using
      (MeasureTheory.ae_restrict_of_forall_mem (μ := volume) (s := Ioi (1 : ℝ)) hmeas hforall)
                                                                               
  have hg_intOn : IntegrableOn g (Ioi (1 : ℝ)) := by
    classical
    by_contra hnot
    have hnot' : ¬ Integrable g μ := by simpa [μ, IntegrableOn] using hnot
    have hint0 : (∫ u, g u ∂μ) = 0 := by
      simpa using (integral_undef (μ := μ) (f := g) hnot')
    have hval : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
      simpa [hgdef] using lem_integralBoundValue s (by linarith [hs_re])
    have hne : (1 / s.re) ≠ 0 := by exact one_div_ne_zero (ne_of_gt (by linarith [hs_re]))
    have : (∫ u in Ioi (1 : ℝ), g u) = 0 := by simpa [μ] using hint0
    exact hne (by simpa [hval] using this)
  have hg_int : Integrable g μ := by simpa [μ, IntegrableOn] using hg_intOn
                                                             
  have h_int_bound : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ∫ u in Ioi (1 : ℝ), g u := by
    have :=
      (MeasureTheory.norm_integral_le_of_norm_le (μ := μ) (f := f) (g := g) hg_int h_ae_bound)
    simpa [μ] using this
                                                                      
  have h_g_val : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
    simpa [hgdef] using lem_integralBoundValue s (by linarith [hs_re])
  have h_int_bound_conc : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ 1 / s.re := by
    simpa [h_g_val] using h_int_bound
                        
  have hmul : ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ‖s‖ * (1 / s.re) := by
    exact mul_le_mul_of_nonneg_left h_int_bound_conc (by exact norm_nonneg s)
                        
  have hsum0 : (1 + ‖1 / (s - 1)‖) + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ (1 + ‖1 / (s - 1)‖) + ‖s‖ * (1 / s.re) := by
    exact add_le_add_right hmul (1 + ‖1 / (s - 1)‖)
  have hsum : 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) := by
    simpa [add_assoc] using hsum0
                                                          
  have hfinal1 : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) :=
    le_trans hζ hsum
  simpa [div_eq_mul_inv] using hfinal1

lemma lem_sOverSminus1Bound (s : ℂ) (_hs : s ≠ 1) : ‖(1 / (s - 1))‖ = 1 / ‖s - 1‖ := by simp [one_div]

lemma lem_zetaBound3 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  simpa [lem_sOverSminus1Bound s hs_ne] using lem_zetaBound2 s hs_re hs_ne

lemma helper_normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq, pow_two] using (Complex.normSq_eq_norm_sq z).symm

lemma helper_three_abs_sq (t : ℝ) : (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  have hnonneg : 0 ≤ (6 : ℝ) * |t| := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact mul_nonneg h6 (abs_nonneg t)
  have hmul : |t| * |t| = t * t := by
    simp
  calc
    (3 : ℝ) ^ 2 + t ^ 2 = (3 : ℝ) ^ 2 + t * t := by simp [pow_two]
    _ = (3 : ℝ) ^ 2 + |t| * |t| := by simp [hmul]
    _ ≤ (3 : ℝ) ^ 2 + |t| * |t| + (6 : ℝ) * |t| := by exact le_add_of_nonneg_right hnonneg
    _ = (3 + |t|) ^ 2 := by ring

lemma lem_sBound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) : ‖s‖ < (3 : ℝ) + |s.im| := by
  have hnegthree_lt_re : (- (3 : ℝ)) < s.re := by
    have hlt : (- (3 : ℝ)) < (1 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hlt hs.1
  have hlt3 : s.re < (3 : ℝ) := hs.2
  have h_re_sq_lt : s.re ^ 2 < (3 : ℝ) ^ 2 := by
    simpa using (sq_lt_sq' hnegthree_lt_re hlt3)
  have hsumlt : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := by
    exact add_lt_add_left h_re_sq_lt _
  have hsq : ‖s‖ ^ 2 < (3 + |s.im|) ^ 2 := by
    have h := lt_of_lt_of_le hsumlt (helper_three_abs_sq s.im)
    simpa [helper_normsq s] using h
  have hnormnn : 0 ≤ ‖s‖ := norm_nonneg _
  have hpos : 0 ≤ (3 : ℝ) + |s.im| := add_nonneg (by norm_num) (abs_nonneg _)
  exact (sq_lt_sq₀ hnormnn hpos).1 hsq

lemma lem_invReSbound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have h_pos : (0 : ℝ) < s.re := by
    linarith [hs.1]
  have h_half_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have h_recip : 1 / s.re ≤ 1 / (1/2 : ℝ) := one_div_le_one_div_of_le h_half_pos hs.1
  have h_simplify : 1 / (1/2 : ℝ) = (2 : ℝ) := by norm_num
  rw [h_simplify] at h_recip
  exact h_recip

lemma lem_invSminus1bound (s : ℂ) (_hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : (1 : ℝ) ≤ ‖s - 1‖ := by
  have h2 : |s.im| ≤ ‖s - 1‖ := by
    have : (s - (1 : ℂ)).im = s.im := by
      simp [Complex.sub_im, Complex.one_im]
    simpa [this] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im h2

lemma reciprocal_le_one_of_one_le {x : ℝ} (hx_pos : 0 < x) (hx_ge : 1 ≤ x) : 1 / x ≤ 1 := by
                                                            
  have h_div_pos : 0 < 1 / x := one_div_pos.mpr hx_pos
                                     
  have h1 : (1 / x) * 1 ≤ (1 / x) * x := by
    exact mul_le_mul_of_nonneg_left hx_ge (le_of_lt h_div_pos)
                                                
  rw [mul_one] at h1
  rw [one_div_mul_cancel (ne_of_gt hx_pos)] at h1
  exact h1

lemma div_le_mul_of_one_div_le {a c d : ℝ} (ha : 0 ≤ a) (_hc : 0 < c) (h : 1 / c ≤ d) : a / c ≤ a * d := by
                                 
  rw [div_eq_mul_one_div]
                                                                  
  exact mul_le_mul_of_nonneg_left h ha

lemma lem_finalBoundCombination (s : ℂ) (hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : ‖riemannZeta s‖ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
                                                                                   
  have hs_ne : s ≠ 1 := by
    intro h
    rw [h] at hs_im
    simp at hs_im
    linarith
                                  
  have hs_re_pos : 0 < s.re := by linarith [hs_re.1]
                                               
  have h1 : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := lem_zetaBound3 s (by linarith [hs_re_pos]) hs_ne
                                                   
  have h2 : (1 : ℝ) ≤ ‖s - 1‖ := lem_invSminus1bound s hs_re hs_im
  have h3 : 1 / ‖s - 1‖ ≤ 1 := reciprocal_le_one_of_one_le (by linarith [h2]) h2
                                             
  have h4 : ‖s‖ < (3 : ℝ) + |s.im| := lem_sBound s hs_re
                                            
  have h5 : 1 / s.re ≤ (2 : ℝ) := lem_invReSbound s hs_re
                                  
  calc ‖riemannZeta s‖
    ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := h1
    _ ≤ 1 + 1 + ‖s‖ / s.re := by linarith [h3]
    _ ≤ 1 + 1 + ‖s‖ * 2 := by
      have s_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
      exact add_le_add_right (div_le_mul_of_one_div_le s_nonneg hs_re_pos h5) _
    _ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by linarith [h4]

lemma lem_finalAlgebra (t : ℝ) : 1 + 1 + ((3 : ℝ) + |t|) * 2 = (8 : ℝ) + 2 * |t| := by ring

lemma lem_zetaUppBd (z : ℂ) (hz_re : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  have hz_re' : (1/2 : ℝ) ≤ z.re ∧ z.re < (3 : ℝ) := by
    simpa [Ico] using hz_re
  have h := lem_finalBoundCombination z hz_re' hz_im
  simpa [lem_finalAlgebra] using h

lemma lem_zfroms_calc (s : ℂ) (t : ℝ) :
    (let z := s + (3/2 : ℝ) + I * t
     z.re = s.re + (3/2 : ℝ) ∧ z.im = s.im + t) := by
  constructor
  ·                           
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
                                                                       
    have h1 : I.re = 0 := Complex.I_re
    have h2 : I.im * 0 = 0 := mul_zero _
    rw [h1, h2]
    simp
  ·                   
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
                                                                   
    have h1 : I.re * 0 = 0 := mul_zero _
    have h2 : I.im = 1 := Complex.I_im
    rw [h1, h2]
    simp

lemma lem_zfroms_conditions (s : ℂ) (t : ℝ)
    (hs : ‖s‖ ≤ (1 : ℝ)) (ht : (2 : ℝ) < |t|) :
    (let z := s + (3/2 : ℝ) + I * t
     z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im|) := by
                                                        
  have h_calc := lem_zfroms_calc s t
  simp only [h_calc.1, h_calc.2]
  constructor

  ·                                                   
                                                                
    have hs_re_bound : |s.re| ≤ 1 :=
      (Complex.abs_re_le_norm s).trans hs
    rw [abs_le] at hs_re_bound

    rw [Set.mem_Ico]
    constructor
    ·                                     
      linarith [hs_re_bound.1]
    ·                                    
      linarith [hs_re_bound.2]

  ·                                            
    have hs_im_bound : |s.im| ≤ 1 :=
      (Complex.abs_im_le_norm s).trans hs
    rw [abs_le] at hs_im_bound

    by_cases h : 0 ≤ t
    ·                                        
      have ht_pos : t > 2 := by
        rwa [abs_of_nonneg h] at ht
                                       
      have lower_bound : s.im + t ≥ 1 := by
        linarith [hs_im_bound.1, ht_pos]
      have nonneg : 0 ≤ s.im + t := by linarith
      rw [abs_of_nonneg nonneg]
      linarith [lower_bound]
    ·                                                     
      push Not at h
      have ht_neg : t < -2 := by
        rw [abs_of_neg h] at ht
        linarith [ht]
                                                                 
      have upper_bound : s.im + t ≤ -1 := by
        linarith [hs_im_bound.2, ht_neg]
      have neg : s.im + t < 0 := by linarith
      rw [abs_of_neg neg]
      linarith [upper_bound]

lemma lem_abs_im_bound (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) : |s.im + t| ≤ 1 + |t| := by
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ 1 := le_trans h1 hs
  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add_le s.im t
  linarith

lemma lem_zetaUppBound :
    ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ (1 : ℝ) → (2 : ℝ) < |t| →
      ‖riemannZeta (s + (3/2 : ℝ) + I * t)‖ < (10 : ℝ) + 2 * |t| := by
  intro t s hs ht
  set z := s + (3/2 : ℝ) + I * t with hz_def
                                                       
  have hz_cond : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| :=
    lem_zfroms_conditions s t hs ht
                        
  have h_bound : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| :=
    lem_zetaUppBd z hz_cond.1 hz_cond.2
                                         
  have hz_im_calc : z.im = s.im + t := (lem_zfroms_calc s t).2
  have h_im_bound : |z.im| ≤ 1 + |t| := by
    rw [hz_im_calc]
    exact lem_abs_im_bound s t hs
                   
  have h_intermediate : ‖riemannZeta z‖ < (8 : ℝ) + 2 * (1 + |t|) := by
    calc ‖riemannZeta z‖
      < (8 : ℝ) + 2 * |z.im| := h_bound
      _ ≤ (8 : ℝ) + 2 * (1 + |t|) := by linarith [h_im_bound]
                           
  have h_algebra : (8 : ℝ) + 2 * (1 + |t|) = (10 : ℝ) + 2 * |t| := by ring
                
  have h_final : ‖riemannZeta z‖ < (10 : ℝ) + 2 * |t| := by
    linarith [h_intermediate, h_algebra]
                                                
  rwa [hz_def] at h_final

open Metric _root_.Set Filter Asymptotics BigOperators

noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

def zerosetKfRc (R : ℝ) (c : ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall c R ∧ f ρ = 0}

lemma zetadiffAtnot1 : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s :=
  fun _ => differentiableAt_riemannZeta

lemma DiffAtWithinAt {T : Set ℂ} {g : ℂ → ℂ} {s : ℂ} (_hs : s ∈ T) :
    DifferentiableAt ℂ g s → DifferentiableWithinAt ℂ g T s :=
  DifferentiableAt.differentiableWithinAt

lemma DiffWithinAtallOn {T : Set ℂ} {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableWithinAt ℂ g T s) → DifferentiableOn ℂ g T := fun h => h

lemma DiffAtOn {T : Set ℂ} {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableAt ℂ g s) → DifferentiableOn ℂ g T := by
  intro h s hs
  exact (h s hs).differentiableWithinAt

lemma DiffOnanalOnNhd {T : Set ℂ} (hT : IsOpen T) {g : ℂ → ℂ} :
    DifferentiableOn ℂ g T → AnalyticOnNhd ℂ g T := by
  intro hdiff
  exact hdiff.analyticOnNhd hT

lemma DiffAtallanalOnNhd {T : Set ℂ} (hT : IsOpen T) {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableAt ℂ g s) → AnalyticOnNhd ℂ g T := by
  intro hdiff
  apply DiffOnanalOnNhd hT
  exact DiffAtOn hdiff

lemma zetaanalOnnot1 : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  apply DiffAtallanalOnNhd
  · apply isOpen_compl_singleton
  · exact zetadiffAtnot1

lemma I_mul_ofReal_im (t : ℝ) : (I * ↑t).im = t := by
  have h1 : (I * (↑t : ℂ)).im = (↑t : ℂ).re := Complex.I_mul_im (↑t : ℂ)
  rw [h1]
  simp [Complex.ofReal_re]

lemma complex_im_sub_I_mul (a : ℂ) (t : ℝ) : (a - I * t).im = a.im - t := by
  rw [Complex.sub_im]
  rw [I_mul_ofReal_im]

lemma D1cinTt_pre (t : ℝ) (ht : |t| > 1) :
    ∀ s ∈ closedBall (3/2 + I * t : ℂ) 1, s ≠ 1 := by
  intro s hs
  by_contra h
                                                   
  rw [h] at hs
                                            
  rw [mem_closedBall] at hs
                                  
  rw [Complex.dist_eq] at hs

  have h1 : (1 : ℂ) - (3/2 + I * t) = -1/2 - I * t := by ring
  rw [h1] at hs

  have h2 : (-1/2 - I * t : ℂ).im = -t := by
    have : (-1/2 - I * t : ℂ) = (-1/2 : ℂ) - I * t := by ring
    rw [this]
    rw [complex_im_sub_I_mul]
    simp

  have h3 : ‖(-1/2 - I * t : ℂ)‖ ≥ |(-1/2 - I * t : ℂ).im| := Complex.abs_im_le_norm _

  rw [h2] at h3
  rw [abs_neg] at h3

  have h4 : ‖(-1/2 - I * t : ℂ)‖ > 1 := lt_of_lt_of_le ht h3

  linarith [h4, hs]

lemma D1cinTt (t : ℝ) (ht : |t| > 1) :
    closedBall (3/2 + I * t : ℂ) 1 ⊆ {s : ℂ | s ≠ 1} := by
                                           
  exact fun s hs => D1cinTt_pre t ht s hs

lemma zetaanalOnD1c (t : ℝ) (ht : |t| > 1) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (3/2 + I * t : ℂ) 1) := by
  apply zetaanalOnnot1.mono
  exact D1cinTt t ht

lemma zetaanalOnD1c_general (x t : ℝ) (ht : |t| > 1) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (x + I * t : ℂ) 1) := by
  apply zetaanalOnnot1.mono
                                                         
  intro s hs
  by_contra h
                                                 
  have h' : s = 1 := by
    simp at h
    exact h
  rw [h'] at hs
  rw [mem_closedBall] at hs
  rw [Complex.dist_eq] at hs
                               
  have h1 : (1 : ℂ) - (x + I * t) = (1 - x) - I * t := by ring
  rw [h1] at hs
                             
  have h2 : ((1 - x) - I * t : ℂ).im = -t := by
    rw [Complex.sub_im]
    rw [Complex.sub_im]
    rw [Complex.ofReal_im]
    rw [I_mul_ofReal_im]
    simp
                      
  have h3 : ‖((1 - x) - I * t : ℂ)‖ ≥ |((1 - x) - I * t : ℂ).im| := Complex.abs_im_le_norm _
  rw [h2] at h3
  rw [abs_neg] at h3
                                                         
  have h4 : ‖((1 - x) - I * t : ℂ)‖ > 1 := lt_of_lt_of_le ht h3
                                            
  linarith

lemma sigmageq1 (s : ℂ) (hs : s.re > 1) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

lemma Complex_I_mul_ofReal_re (r : ℝ) : (I * (r : ℂ)).re = 0 := by
  have h : (I * (r : ℂ)).re = -(r : ℂ).im := Complex.I_mul_re (r : ℂ)
  rw [h]
  simp

lemma re_real_add_I_mul_gt (a b : ℝ) (h : a > 1) : (a + I * b).re > 1 := by
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex_I_mul_ofReal_re]
  simp
  exact h

lemma zetacnot0 (t : ℝ) : riemannZeta (3/2 + I * t) ≠ 0 := by
  apply sigmageq1
  apply re_real_add_I_mul_gt
  norm_num

lemma zetacnot0_general (x t : ℝ) (hx : x > 1) : riemannZeta (x + I * t) ≠ 0 := by
  apply sigmageq1
  apply re_real_add_I_mul_gt
  exact hx

lemma fc_analytic_normalized (c : ℂ) (f : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    (AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (closedBall (0 : ℂ) 1)) ∧ (fun z => f (z + c) / f c) 0 = 1 := by
  constructor
  ·                                  
    apply AnalyticOnNhd.div
    ·                                                  
      apply AnalyticOnNhd.comp h_analytic
      ·                          
        intro z _
        exact analyticAt_id.add analyticAt_const
      ·                                                    
        intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [Complex.dist_eq] at hz ⊢
                                                   
        convert hz using 1
        ring_nf
    ·                                          
      exact analyticOnNhd_const
    ·                           
      intro z _
      exact h_nonzero
  ·                                              
    simpa using h_nonzero

lemma deriv_normalized_nohd (c : ℂ) (f : ℂ → ℂ) (z : ℂ) (_h_nonzero : f c ≠ 0) :
  deriv (fun w => f (w + c) / f c) z = (deriv f (z + c)) / f c := by
  rw [deriv_div_const]
  rw [deriv_comp_add_const]

lemma frac_cancel_const {x y c : ℂ} (hc : c ≠ 0) (hy : y ≠ 0) : (x / c) / (y / c) = x / y := by
  field_simp [hc, hy]

lemma fc_log_deriv (c : ℂ) (f : ℂ → ℂ)
    (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0)
    {z : ℂ} (hz_nonzero : f (z + c) ≠ 0) :
    (deriv (fun w => f (w + c) / f c) z) / (f (z + c) / f c) = (deriv f (z + c)) / f (z + c) := by
                                                                  
  rw [deriv_normalized_nohd c f z h_nonzero]

  rw [frac_cancel_const h_nonzero hz_nonzero]

lemma fc_bound (B : ℝ) (_hB : B > 1) (R : ℝ) (_hRpos : 0 < R) (_hR : R < 1) (c : ℂ) (f : ℂ → ℂ) (_h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by
    simpa [mem_closedBall, Complex.dist_eq] using hz
  have hz_plus : z + c ∈ closedBall c R := by
    have : ‖(z + c) - c‖ ≤ R := by simpa [add_sub_cancel] using hz'
    simpa [mem_closedBall, Complex.dist_eq] using this
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_plus
  have hnorm : ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖ := by
    simp [div_eq_mul_inv, norm_inv]
  have : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ :=
    div_le_div_of_nonneg_right hfb (norm_nonneg _)
  simpa [hnorm] using this

lemma fc_zeros (r : ℝ) (_h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
  (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  ext ρ'; constructor
  · intro hmem
    rcases hmem with ⟨hball, hzero⟩
                                                                     
    have hprod : f (ρ' + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using hzero
    have hnum0 : f (ρ' + c) = 0 := by
      rcases mul_eq_zero.mp hprod with hnum | hinv
      · exact hnum
      · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
        exact (this hinv).elim
    refine ⟨ρ' + c, ?_, ?_⟩
    ·                                   
      have hdist0 : dist ρ' (0 : ℂ) ≤ r := by simpa [mem_closedBall] using hball
      have hdist1 : dist (ρ' + c) c ≤ r := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist0
      have hmem_ball : ρ' + c ∈ closedBall c r := by
        simpa [mem_closedBall] using hdist1
      exact And.intro hmem_ball hnum0
    ·                     
      simp
  · intro him
    rcases him with ⟨y, hy_mem, hy_eq⟩
                                           
    subst hy_eq
    rcases hy_mem with ⟨hy_ball, hy_zero⟩
    refine And.intro ?_ ?_
    ·                            
      have hdist : dist y c ≤ r := by simpa [mem_closedBall] using hy_ball
      have hdist0 : dist (y - c) (0 : ℂ) ≤ r := by
        simpa [Complex.dist_eq, sub_zero] using hdist
      simpa [mem_closedBall] using hdist0
    ·                             
      simp [sub_add_cancel, hy_zero]

lemma analyticOrderAt_const_mul_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => a * f z) z0 = analyticOrderAt f z0 := by
  classical
  by_cases hf : AnalyticAt ℂ f z0
  ·                                                  
    have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const (x := z0) (v := a))
    have hconst_order_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
                                     
      refine (AnalyticAt.analyticOrderAt_eq_natCast (f := fun _ : ℂ => a) (z₀ := z0) hconst).mpr ?_
      refine ⟨(fun _ : ℂ => a), (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0), ?_, ?_⟩
      · simpa using ha
      · exact Filter.Eventually.of_forall (fun _ => by simp)
    have hmul := analyticOrderAt_mul (f := fun _ : ℂ => a) (g := f) hconst hf
                                              
    simpa [hconst_order_zero, zero_add] using! hmul
  ·                                                                                         
    have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const (x := z0) (v := a))
    have hconst_ne : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
    have hiff := (analyticAt_iff_analytic_fun_mul (f := fun _ : ℂ => a) (g := f) (z := z0) hconst hconst_ne)
    have hmul : ¬ AnalyticAt ℂ (fun z => a * f z) z0 := by
      intro h
      have : AnalyticAt ℂ f z0 := (hiff.mpr (by simpa using h))
      exact hf this

    simp [analyticOrderAt, hf, hmul]

lemma AnalyticAt.comp_add_const {f : ℂ → ℂ} {z0 c : ℂ} (hf : AnalyticAt ℂ f (z0 + c)) : AnalyticAt ℂ (fun z => f (z + c)) z0 := by
                                                   
  have hinner : AnalyticAt ℂ (fun z : ℂ => z + c) z0 := by
    have h_id : AnalyticAt ℂ (fun z : ℂ => z) z0 := by
      simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) z0)
    have h_const : AnalyticAt ℂ (fun _ : ℂ => c) z0 := by
      simpa using (analyticAt_const (v := c) (x := z0))
    simpa using (AnalyticAt.fun_add (f := fun z : ℂ => z) (g := fun _ : ℂ => c) (x := z0) h_id h_const)
                                   
  simpa using (AnalyticAt.fun_comp (x := z0) hf hinner)

lemma AnalyticAt.of_comp_add_const {f : ℂ → ℂ} {z0 c : ℂ}
    (hg : AnalyticAt ℂ (fun z => f (z + c)) z0) :
    AnalyticAt ℂ f (z0 + c) := by
                                                 
  have hT : AnalyticAt ℂ (fun z => z - c) (z0 + c) := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => z) (z0 + c) := by
      simpa using! (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) (z0 + c))
    have h2 : AnalyticAt ℂ (fun _ : ℂ => -c) (z0 + c) := by
      simpa using (analyticAt_const (x := (z0 + c)) (v := (-c : ℂ)))
    have : AnalyticAt ℂ (fun z => z + (-c)) (z0 + c) := by
      simpa using (AnalyticAt.fun_add h1 h2)
    simpa [sub_eq_add_neg] using this
                                                               
  have hx : (z0 + c) - c = z0 := by simp
  have hg' : AnalyticAt ℂ (fun z => f (z + c)) ((z0 + c) - c) := by
    simpa [hx] using hg
                                                         
  have hcomp :=
    (AnalyticAt.comp (g := (fun z => f (z + c))) (f := (fun z => z - c)) (x := z0 + c)
      hg' hT)
  have hgf : ((fun z => f (z + c)) ∘ (fun z => z - c)) = f := by
    funext z
    simp [Function.comp, sub_eq_add_neg]
  simpa [hgf] using hcomp

lemma order_top_iff_comp_add (f : ℂ → ℂ) (z0 c : ℂ) :
    analyticOrderAt (fun z => f (z + c)) z0 = ⊤ ↔ analyticOrderAt f (z0 + c) = ⊤ := by
  classical
  let g : ℂ → ℂ := fun z => f (z + c)
                                                           
  have eq_left : analyticOrderAt g z0 = ⊤ ↔ ∀ᶠ z in nhds z0, g z = 0 := by
    simpa [g] using (analyticOrderAt_eq_top (f := g))
  have eq_right : analyticOrderAt f (z0 + c) = ⊤ ↔ ∀ᶠ w in nhds (z0 + c), f w = 0 := by
    simpa using (analyticOrderAt_eq_top (f := f))
  constructor
  · intro htop
    have hz : ∀ᶠ z in nhds z0, g z = 0 := (eq_left.mp htop)
                               
    have hcont_sub : ContinuousAt (fun w : ℂ => w - c) (z0 + c) := by
      simpa [sub_eq_add_neg] using!
        ((continuousAt_id).add (continuousAt_const : ContinuousAt (fun _ : ℂ => -c) (z0 + c)))
    have htend : Tendsto (fun w : ℂ => w - c) (nhds (z0 + c)) (nhds ((z0 + c) - c)) :=
      hcont_sub.tendsto
    have hz' : ∀ᶠ w in nhds ((z0 + c) - c), g w = 0 := by
      simpa [sub_eq_add_neg, add_sub_cancel] using hz
    have hw : ∀ᶠ w in nhds (z0 + c), g (w - c) = 0 := htend.eventually hz'
    have hw' : ∀ᶠ w in nhds (z0 + c), f w = 0 := by
      simpa [g, sub_add_cancel] using hw
    exact eq_right.mpr hw'
  · intro htop
    have hw : ∀ᶠ w in nhds (z0 + c), f w = 0 := (eq_right.mp htop)
                               
    have hcont_add : ContinuousAt (fun z : ℂ => z + c) z0 :=
      by simpa using! ((continuousAt_id).add (continuousAt_const : ContinuousAt (fun _ : ℂ => c) z0))
    have htend : Tendsto (fun z : ℂ => z + c) (nhds z0) (nhds (z0 + c)) :=
      hcont_add.tendsto
    have hz : ∀ᶠ z in nhds z0, f (z + c) = 0 := htend.eventually hw
    have hz' : ∀ᶠ z in nhds z0, g z = 0 := by simpa [g] using hz
    exact eq_left.mpr hz'

lemma enat_le_iff_forall_nat {x y : ℕ∞} : x ≤ y ↔ ∀ n : ℕ, (n : ℕ∞) ≤ x → (n : ℕ∞) ≤ y := by
  classical
  constructor
  · intro hxy n hnx
    exact le_trans hnx hxy
  · intro h
    by_cases hx : x = ⊤
    ·                                                           
      subst hx
                                                      
      by_contra hnot
      have hy_ne : y ≠ ⊤ := by
        simpa [WithTop.top_le_iff] using hnot
      obtain ⟨m, hm⟩ := (WithTop.ne_top_iff_exists).1 hy_ne
                                                                   
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ y := h (m + 1) (by simp)
                        
      have h'' : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        simpa [← hm]
          using! h'
                                          
      have : m + 1 ≤ m := (WithTop.coe_le_coe).1 h''
      exact Nat.not_succ_le_self m this
    ·                               
      obtain ⟨k, hk'⟩ := (WithTop.ne_top_iff_exists).1 hx
      have hk : x = (k : ℕ∞) := hk'.symm
                                                                                              
      have hxk : ((k : ℕ∞) ≤ y) := h k (by simp [hk])
                       
      simpa [hk] using hxk

lemma natCast_le_order_const_mul_iff (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) (n : ℕ) :
    (n : ℕ∞) ≤ analyticOrderAt (fun z => a * f z) z0 ↔ (n : ℕ∞) ≤ analyticOrderAt f z0 := by
  constructor
  · intro h
    simpa [analyticOrderAt_const_mul_eq f a z0 ha] using h
  · intro h
    simpa [analyticOrderAt_const_mul_eq f a z0 ha] using h

lemma order_top_iff_const_mul (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => a * f z) z0 = ⊤ ↔ analyticOrderAt f z0 = ⊤ := by
  simp [analyticOrderAt_const_mul_eq (f := f) (a := a) (z0 := z0) ha]

lemma analyticOrderAt_mul_const_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => f z * a) z0 = analyticOrderAt f z0 := by
  classical
                                                             
  have hcomm : (fun z => f z * a) = (fun z => a * f z) := by
    funext z; simp [mul_comm]
  have hrew : analyticOrderAt (fun z => f z * a) z0 =
      analyticOrderAt (fun z => a * f z) z0 := by
    simp [hcomm]
  by_cases hf : AnalyticAt ℂ f z0
  ·                                                                        
    have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
    have hadd : analyticOrderAt (fun z => a * f z) z0
        = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := by
      simpa using! (analyticOrderAt_mul hconst hf)
                                          
    have hconst_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
      have hiff := (AnalyticAt.analyticOrderAt_eq_zero hconst)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
      exact hiff.mpr hval
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := hadd
      _ = 0 + analyticOrderAt f z0 := by simp [hconst_zero]
      _ = analyticOrderAt f z0 := by simp
  ·                                                               
    have hnot : ¬ AnalyticAt ℂ (fun z => a * f z) z0 := by
      intro hmul
      have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
        simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
                                                                
      have hiff := (analyticAt_iff_analytic_fun_smul (h₁f := hconst) (h₂f := hval)
                        (g := f) (z := z0))
      have hsmul : AnalyticAt ℂ (fun z => (fun _ : ℂ => a) z • f z) z0 := by
                                       
        simpa [smul_eq_mul] using hmul
      have : AnalyticAt ℂ f z0 := hiff.mpr hsmul
      exact hf this
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = 0 := by simp [analyticOrderAt, hnot]
      _ = analyticOrderAt f z0 := by simp [analyticOrderAt, hf]

lemma fc_m_order (r : ℝ) (_h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
    (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1))
    {ρ' : ℂ} (_hρ' : ρ' ∈ zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) :
    analyticOrderAt (fun z => f (z + c) / f c) ρ' = analyticOrderAt f (ρ' + c) := by
  classical
                                     
  set g0 : ℂ → ℂ := fun z => f (z + c) with hg0
                                                                                                 
  have hconst : analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' = analyticOrderAt g0 ρ' := by
    have hne : (1 / f c) ≠ 0 := one_div_ne_zero h_nonzero
    simpa using (analyticOrderAt_mul_const_eq (f := g0) (a := (1 / f c)) (z0 := ρ') hne)
  have hconst_rewrite : analyticOrderAt (fun z => f (z + c) / f c) ρ'
        = analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' := by
    have : (fun z => f (z + c) / f c) = (fun z => g0 z * (1 / f c)) := by
      funext z; simp [g0, div_eq_mul_inv, mul_comm]
    simp [this]
                                        
  have htrans : analyticOrderAt g0 ρ' = analyticOrderAt f (ρ' + c) := by
                                          
    by_cases hfA : AnalyticAt ℂ f (ρ' + c)
    ·                                                          
      have h_add : AnalyticAt ℂ (fun z : ℂ => z + c) ρ' := by
        simpa using! (AnalyticAt.add (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) ρ')
                                    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) ρ'))
      have hgA : AnalyticAt ℂ g0 ρ' := by
        have : AnalyticAt ℂ f ((fun z : ℂ => z + c) ρ') := by simpa using hfA
        simpa [g0, hg0] using! (AnalyticAt.comp (g := f) (f := fun z : ℂ => z + c) (x := ρ') this h_add)
                                                         
      by_cases hgez : (∀ᶠ z in nhds ρ', g0 z = 0)
      ·                                                                                      
        have hT_sub_cont : ContinuousAt (fun w : ℂ => w - c) (ρ' + c) := by
          simpa using! (ContinuousAt.sub (continuousAt_id : ContinuousAt (fun w : ℂ => w) (ρ' + c))
                                        (continuousAt_const : ContinuousAt (fun _ : ℂ => c) (ρ' + c)))
        have hT_sub : Tendsto (fun w : ℂ => w - c) (nhds (ρ' + c)) (nhds ρ') := by
          simpa using (hT_sub_cont.tendsto)
        have hEfw : ∀ᶠ w in nhds (ρ' + c), f w = 0 := by
          have : ∀ᶠ w in nhds (ρ' + c), g0 (w - c) = 0 := hT_sub.eventually hgez
                                       
          simpa [g0, hg0, sub_add_cancel] using this
                                                                       
        have hg_top : analyticOrderAt g0 ρ' = ⊤ :=
          (analyticOrderAt_eq_top (f := g0) (z₀ := ρ')).2 hgez
        have hf_top : analyticOrderAt f (ρ' + c) = ⊤ :=
          (analyticOrderAt_eq_top (f := f) (z₀ := ρ' + c)).2 hEfw
        simp [hg_top, hf_top]
      ·                                                                       
        have h_exists := (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hgA).mpr hgez
        rcases h_exists with ⟨n, φ, hφA, hφ_ne, hevent⟩
                                         
        have hT_sub_cont : ContinuousAt (fun w : ℂ => w - c) (ρ' + c) := by
          simpa using! (ContinuousAt.sub (continuousAt_id : ContinuousAt (fun w : ℂ => w) (ρ' + c))
                                        (continuousAt_const : ContinuousAt (fun _ : ℂ => c) (ρ' + c)))
        have hT_sub : Tendsto (fun w : ℂ => w - c) (nhds (ρ' + c)) (nhds ρ') := by
          simpa using (hT_sub_cont.tendsto)
        have hevent_w : ∀ᶠ w in nhds (ρ' + c), f w
              = (w - (ρ' + c)) ^ n * ((fun w => φ (w - c)) w) := by
          have : ∀ᶠ w in nhds (ρ' + c), g0 (w - c)
                    = ((w - c) - ρ') ^ n * φ (w - c) :=
            hT_sub.eventually hevent
                                                                         
          refine this.mono ?_
          intro w hw
          have hsubsimp : (w - c) - ρ' = w - (ρ' + c) := by ring
          simpa [g0, hg0, hsubsimp] using hw
                                                                               
        have hψA : AnalyticAt ℂ (fun w => φ (w - c)) (ρ' + c) := by
          have h_subA : AnalyticAt ℂ (fun w : ℂ => w - c) (ρ' + c) := by
            simpa using! (AnalyticAt.sub (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) (ρ' + c))
                                        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) (ρ' + c)))
          have hφA_at : AnalyticAt ℂ φ ((fun w : ℂ => w - c) (ρ' + c)) := by simpa using hφA
          simpa using! (AnalyticAt.comp (g := φ) (f := fun w => w - c) (x := (ρ' + c)) hφA_at h_subA)
        have hψ_ne : (fun w => φ (w - c)) (ρ' + c) ≠ 0 := by
                                      
          simpa using hφ_ne
                                                                   
        have hg_eq_n : analyticOrderAt g0 ρ' = n := by
          exact (AnalyticAt.analyticOrderAt_eq_natCast (f := g0) (z₀ := ρ') hgA).mpr
            ⟨φ, hφA, hφ_ne, hevent⟩
        have hf_eq_n : analyticOrderAt f (ρ' + c) = n := by
          exact (AnalyticAt.analyticOrderAt_eq_natCast (f := f) (z₀ := ρ' + c) hfA).mpr
            ⟨(fun w => φ (w - c)), hψA, hψ_ne, hevent_w⟩
        simp [hg_eq_n, hf_eq_n]
    ·                                                                        
      have hg_not : ¬ AnalyticAt ℂ g0 ρ' := by
        intro hgA
                                                                      
        have h_subA : AnalyticAt ℂ (fun w : ℂ => w - c) (ρ' + c) := by
          simpa using! (AnalyticAt.sub (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) (ρ' + c))
                                      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) (ρ' + c)))
        have hgA_at : AnalyticAt ℂ g0 ((ρ' + c) - c) := by simpa using hgA
        have hcomp := (AnalyticAt.comp (g := g0) (f := fun w => w - c)
                          (x := (ρ' + c)) hgA_at h_subA)
                                    
        have : AnalyticAt ℂ (fun w : ℂ => g0 (w - c)) (ρ' + c) := by simpa using! hcomp
        have : AnalyticAt ℂ f (ρ' + c) := by
          simpa [g0, hg0, sub_add_cancel] using this
        exact hfA this
                                                                       
      simp [analyticOrderAt, hfA, hg_not]
                                                                                      
  calc
    analyticOrderAt (fun z => f (z + c) / f c) ρ'
        = analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' := hconst_rewrite
    _ = analyticOrderAt g0 ρ' := hconst
    _ = analyticOrderAt f (ρ' + c) := htrans

lemma DminusK (r1 : ℝ) (R1 : ℝ) (_hr1 : r1 > 0) (_hR1 : R1 > 0) (c : ℂ) (f : ℂ → ℂ)
    (_h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    ∀ z : ℂ, z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun w => f (w + c) / f c) ↔
             z + c ∈ closedBall c r1 \ zerosetKfRc R1 c f := by
  intro z
  constructor
  ·                                                                             
    intro ⟨hz_ball, hz_not_zero⟩
    constructor
    ·                                
      have hdist : dist z (0 : ℂ) ≤ r1 := by simpa [mem_closedBall] using hz_ball
      have hdist_c : dist (z + c) c ≤ r1 := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist
      simpa [mem_closedBall] using hdist_c
    ·                                   
      intro h_contra
      apply hz_not_zero
                                                                                              
      rcases h_contra with ⟨hz_c_ball, hz_c_zero⟩
      constructor
      ·                            
        have hdist_c : dist (z + c) c ≤ R1 := by simpa [mem_closedBall] using hz_c_ball
        have hdist_0 : dist z (0 : ℂ) ≤ R1 := by
          simpa [Complex.dist_eq, add_sub_cancel] using hdist_c
        simpa [mem_closedBall] using hdist_0
      ·                            
        have : f (z + c) = 0 := hz_c_zero
        simp [this, zero_div]
  ·                                                                             
    intro ⟨hz_c_ball, hz_c_not_zero⟩
    constructor
    ·                            
      have hdist_c : dist (z + c) c ≤ r1 := by simpa [mem_closedBall] using hz_c_ball
      have hdist_0 : dist z (0 : ℂ) ≤ r1 := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist_c
      simpa [mem_closedBall] using hdist_0
    ·                                                        
      intro h_contra
      apply hz_c_not_zero
                                                                                              
      rcases h_contra with ⟨hz_ball, hz_zero⟩
      constructor
      ·                                
        have hdist_0 : dist z (0 : ℂ) ≤ R1 := by simpa [mem_closedBall] using hz_ball
        have hdist_c : dist (z + c) c ≤ R1 := by
          simpa [Complex.dist_eq, add_sub_cancel] using hdist_0
        simpa [mem_closedBall] using hdist_c
      ·                      
        have h_div_zero : f (z + c) / f c = 0 := hz_zero
        have h_mul_zero : f (z + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using h_div_zero
        cases' mul_eq_zero.mp h_mul_zero with h_num h_inv
        · exact h_num
        · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
          exact (this h_inv).elim

lemma shifted_zeros_correspondence (R1 : ℝ) (hR1 : R1 > 0) (c z : ℂ)
    (f : ℂ → ℂ) (h_nonzero : f c ≠ 0) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1))
    (hfin_orig : (zerosetKfRc R1 c f).Finite)
    (hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)).Finite) :
    ∑ ρ ∈ hfin_orig.toFinset, ((analyticOrderAt f ρ).toNat : ℂ) / (z - ρ) =
    ∑ ρ' ∈ hfin_shift.toFinset, ((analyticOrderAt (fun u => f (u + c) / f c) ρ').toNat : ℂ) / ((z - c) - ρ') := by
                                                              
  have h_bij : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
    fc_zeros R1 hR1 c f h_nonzero h_analytic

  apply Finset.sum_bij (fun ρ _ => ρ - c)

  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ ⊢
    rw [h_bij]
    use ρ, hρ

  · intro ρ₁ hρ₁ ρ₂ hρ₂ h_eq
                                           
    have : ρ₁ = ρ₁ - c + c := by ring
    rw [this, h_eq]
    ring

  · intro ρ' hρ'
    simp only [Set.Finite.mem_toFinset] at hρ'
    rw [h_bij] at hρ'
    obtain ⟨ρ, hρ_mem, hρ_eq⟩ := hρ'
    use ρ
    simp only [Set.Finite.mem_toFinset]
    exact ⟨hρ_mem, hρ_eq⟩

  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ
                                                   
    have h_shift_mem : ρ - c ∈ zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c) := by
      rw [h_bij]
      use ρ, hρ

    have h_order := fc_m_order R1 hR1 c f h_nonzero h_analytic h_shift_mem
                            
    have h_add : (ρ - c) + c = ρ := by ring
    rw [h_add] at h_order
    rw [← h_order]
                                                               
    ring

lemma final_ineq2
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ < B)
    (hfin : (zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c)).Finite) :
    ∀ z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c),
    ‖(deriv (fun z => f (z + c) / f c) z / (f (z + c) / f c)) - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt (fun w => f (w + c) / f c) ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖f c‖) := by
  intro z hz

  let g : ℂ → ℂ := fun w => f (w + c) / f c

  have hR_pos : 0 < R := by linarith [hr1pos, hr1_lt_r, hr_lt_R1, hR1_lt_R]
  have hR1_pos : 0 < R1 := by linarith [hr1pos, hr1_lt_r, hr_lt_R1]
  have h_norm_pos : 0 < ‖f c‖ := norm_pos_iff.mpr h_nonzero

  have h_fc_bound_at_c : ‖f c‖ < B := by
    apply h_bound
    rw [mem_closedBall, dist_self]
    exact le_of_lt hR_pos

  have h_B_div_gt_one : 1 < B / ‖f c‖ := by
    rw [one_lt_div h_norm_pos]
    exact h_fc_bound_at_c

  have h_g_analytic : ∀ w ∈ closedBall (0 : ℂ) 1, AnalyticAt ℂ g w :=
    (fc_analytic_normalized c f h_analytic h_nonzero).1

  have h_g_zero : g 0 = 1 :=
    (fc_analytic_normalized c f h_analytic h_nonzero).2

  have h_g_bound : ∀ w ∈ closedBall (0 : ℂ) R, ‖g w‖ ≤ B / ‖f c‖ := by
    apply fc_bound B hB R hR_pos hR c f h_nonzero
    intro w hw
    exact le_of_lt (h_bound w hw)

  have h_zeroset_equiv : zerosetKfRc R1 (0 : ℂ) g = zerosetKfR R1 hR1_pos g := by
    ext ρ
    simp only [zerosetKfRc, zerosetKfR, mem_ofPred_eq, mem_closedBall, Complex.dist_eq, sub_zero]

  have h_g_finite : (zerosetKfR R1 hR1_pos g).Finite := by
    rwa [← h_zeroset_equiv]

  have h_σ_exists : ∃ h_σ : ℂ → (ℂ → ℂ), ∀ σ ∈ zerosetKfR R1 hR1_pos g,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ w in nhds σ, g w = (w - σ) ^ (analyticOrderAt g σ).toNat * h_σ σ w := by
                                                                  
    classical
    let h_σ : ℂ → (ℂ → ℂ) := fun σ =>
      if hσ : σ ∈ zerosetKfR R1 hR1_pos g
      then Classical.choose (lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR g h_g_analytic
           (by simp [g]; exact h_nonzero) σ hσ)
      else fun _ => 0
    use h_σ
    intro σ hσ
    simp only [h_σ, dite_eq_left hσ]
    exact Classical.choose_spec (lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR g h_g_analytic
           (by simp [g]; exact h_nonzero) σ hσ)

  obtain ⟨h_σ, h_σ_spec⟩ := h_σ_exists

  have := final_ineq1 (B / ‖f c‖) h_B_div_gt_one r1 r R R1 hr1pos hr1_lt_r hr_lt_R1 hR1_lt_R hR
    g h_g_analytic h_g_zero h_g_finite h_σ_spec h_g_bound z

  have hz_domain : z ∈ closedBall (0 : ℂ) r1 \ zerosetKfR R1 hR1_pos g := by
    rw [h_zeroset_equiv] at hz
    exact hz

  exact this hz_domain

lemma log_Deriv_Expansion_Zeta (t : ℝ) (ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) :
    let c := (3/2 : ℂ) + I * t
    ∀ B > 1, (∀ z ∈ closedBall c R, ‖riemannZeta z‖ < B) →
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
  intro c B hB h_bound hfin z hzmem
                                 
  have ht1 : |t| > 1 := lt_trans (by norm_num : (1 : ℝ) < 2) (by simpa using ht)
                                                                        
  have hζ_analytic : AnalyticOnNhd ℂ riemannZeta (closedBall c 1) := by
    simpa [c] using zetaanalOnD1c t ht1
  have hζ_c_ne : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
                                                                           
  have hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c)).Finite := by
    have h_bij := fc_zeros R1 hR1_pos c riemannZeta hζ_c_ne hζ_analytic
    have himg : ((fun ρ => ρ - c) '' (zerosetKfRc R1 c riemannZeta)).Finite := hfin.image _
    simpa [h_bij] using himg
                                                            
  have hz0mem : (z - c) ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c) := by
    have hiff := DminusK r1 R1 hr1_pos hR1_pos c riemannZeta hζ_analytic hζ_c_ne (z - c)
    exact (hiff).mpr (by simpa [sub_add_cancel] using hzmem)
                                                                  
  have hineq0 :=
    (final_ineq2 B hB r1 r R R1 hr1_pos hr1_lt_r hr_lt_R1 hR1_lt_R hR_lt_1 c riemannZeta
      hζ_analytic hζ_c_ne h_bound hfin_shift) (z - c) hz0mem
                                              
  rcases hzmem with ⟨hz_ball, hz_notin⟩
  have hr1_lt_R1' : r1 < R1 := lt_trans hr1_lt_r hr_lt_R1
  have hz_in_ball_R1 : z ∈ closedBall c R1 := by
    have hz_le_r1 : dist z c ≤ r1 := by simpa [mem_closedBall] using hz_ball
    have hr1_le_R1 : r1 ≤ R1 := le_of_lt hr1_lt_R1'
    have hz_le_R1 : dist z c ≤ R1 := le_trans hz_le_r1 hr1_le_R1
    simpa [mem_closedBall] using hz_le_R1
  have hzeta_ne : riemannZeta z ≠ 0 := by
    intro hz0
    exact hz_notin ⟨hz_in_ball_R1, hz0⟩
                                                    
  have hcancel_frac : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c)
        / (riemannZeta z / riemannZeta c)
        = deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta z := by
    have hc : riemannZeta c ≠ 0 := hζ_c_ne
    have hy : riemannZeta z ≠ 0 := hzeta_ne
    simpa using (frac_cancel_const (x := deriv (fun x => riemannZeta (x + c)) (z - c))
              (y := riemannZeta z) (c := riemannZeta c) hc hy)
  have hcancel_all : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c)
        / (riemannZeta z / riemannZeta c)
        = deriv riemannZeta z / riemannZeta z := by
    simpa [deriv_comp_add_const, sub_add_cancel] using hcancel_frac
                                                                        
  have hineq1 : ‖(deriv riemannZeta z / riemannZeta z)
        - ∑ ρ ∈ hfin_shift.toFinset,
            ((analyticOrderAt (fun u => riemannZeta (u + c) / riemannZeta c) ρ).toNat : ℂ)
              / ((z - c) - ρ)‖
        ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) *
            Real.log (B / ‖riemannZeta c‖) := by
    simpa [hcancel_all] using hineq0
                                                                
  have hsum_eq := shifted_zeros_correspondence R1 hR1_pos c z riemannZeta hζ_c_ne hζ_analytic hfin hfin_shift
                                                                        
  have hineq2 : ‖(deriv riemannZeta z / riemannZeta z)
        - ∑ ρ ∈ hfin.toFinset,
            ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) *
            Real.log (B / ‖riemannZeta c‖) := by
    simpa [hsum_eq] using hineq1
                                                
  simpa [logDerivZeta] using hineq2

lemma zeta32lower : ∃ a > 0, ∀ t : ℝ, ‖riemannZeta (3/2 + I * t)‖ ≥ a := by
  rcases zeta_low_332 with ⟨a, ha_pos, hbound⟩
  refine ⟨a, ha_pos, ?_⟩
  intro t
  simpa [mul_comm] using! (hbound t)

lemma zeta32lower_log : ∃ A > 1, ∀ t : ℝ,
    Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) ≤ A := by
  obtain ⟨a, ha_pos, hbound⟩ := zeta32lower
  refine ⟨max (2 : ℝ) (Real.log (1 / a)), ?_, ?_⟩
  · have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (2 : ℝ) ≤ max (2 : ℝ) (Real.log (1 / a)) := by exact le_max_left _ _
    exact lt_of_lt_of_le h1 h2
  · intro t
    set x := ‖riemannZeta (3/2 + I * t)‖ with hx
    have hax : a ≤ x := by
      simpa [hx] using (hbound t)
    have hxpos : 0 < x := lt_of_lt_of_le ha_pos hax
    have hxy : 1 / x ≤ 1 / a := by
                                               
      have := one_div_le_one_div_of_le ha_pos hax
                                          
      simpa [hx] using this
    have hxpos' : 0 < 1 / x := one_div_pos.mpr hxpos
    have hlog : Real.log (1 / x) ≤ Real.log (1 / a) :=
      Real.log_le_log hxpos' hxy
    have : Real.log (1 / x) ≤ max (2 : ℝ) (Real.log (1 / a)) :=
      le_trans hlog (le_max_right _ _)
    simpa [hx] using this

lemma zeta32upper_pre : ∃ b > 1, ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → (2 : ℝ) < |t| → ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < b * |t| := by
  refine ⟨(12 : ℝ), by norm_num, ?_⟩
  intro t s hs ht
  have hlt : ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < (10 : ℝ) + 2 * |t| := by
    simpa using! (lem_zetaUppBound t s hs ht)
  have honele : (1 : ℝ) ≤ |t| := by
    have : (1 : ℝ) < |t| := lt_trans (by norm_num) ht
    exact le_of_lt this
  have h10le : (10 : ℝ) ≤ 10 * |t| := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right honele (by norm_num : (0 : ℝ) ≤ (10 : ℝ)))
  have hle2 : (10 : ℝ) + 2 * |t| ≤ (12 : ℝ) * |t| := by
    have htmp := add_le_add_left h10le (2 * |t|)
    have hcalc : 10 * |t| + 2 * |t| = (12 : ℝ) * |t| := by ring
    simpa [hcalc] using! htmp
  exact lt_of_lt_of_le hlt hle2

lemma zeta32upper : ∃ b > 1, ∀ t : ℝ, |t| > 2 →
  let c := (3/2 : ℂ) + I * t
  ∀ s ∈ closedBall c 1, ‖riemannZeta s‖ < b * |t| := by
                                         
  obtain ⟨b, hb_gt, hbound⟩ := zeta32upper_pre
  refine ⟨b, hb_gt, ?_⟩
  intro t ht c s hs
                                         
  rw [mem_closedBall] at hs
                                         
  set s_pre := s - c with hs_pre_def
  have hs_pre_bound : ‖s_pre‖ ≤ 1 := by
    rw [hs_pre_def]
    rwa [Complex.dist_eq] at hs
                                            
  have hs_eq : s = s_pre + 3/2 + I * t := by
    rw [hs_pre_def]
    ring
                          
  rw [hs_eq]
  exact hbound t s_pre hs_pre_bound ht

lemma closedBall_subset_unit (c : ℂ) (R : ℝ) (hR_lt_1 : R < 1) :
  Metric.closedBall c R ⊆ Metric.closedBall c 1 := by
  apply Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1)

lemma zeta_c_nonzero (t : ℝ) : riemannZeta (3/2 + I * t) ≠ 0 := by
  exact zetacnot0 t

lemma zeta_c_norm_pos (t : ℝ) : 0 < ‖riemannZeta (3/2 + I * t)‖ := by
  have h := zetacnot0 t
  exact norm_pos_iff.mpr h

lemma Zeta1_Zeta_Expand :
    ∃ A > 1, ∃ b > 1,
    ∀ (t : ℝ) (_ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (_hr1_pos : 0 < r1) (_hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (_hr_lt_R1 : r < R1) (_hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
                                                           
  obtain ⟨b, hbgt1, hb⟩ := zeta32upper
  obtain ⟨A, hAgt1, hA⟩ := zeta32lower_log

  refine ⟨A, hAgt1, b, hbgt1, ?_⟩
  intro t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 c hfin z hz

  have hexp_lemma := log_Deriv_Expansion_Zeta t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1

  have htpos : (0 : ℝ) < |t| := by linarith [ht]
  have hBgt1 : b * |t| > 1 := by
    have hb_pos : (0 : ℝ) < b := by linarith [hbgt1]
    calc (1 : ℝ) < 1 * 2 := by norm_num
    _ < b * 2 := mul_lt_mul_of_pos_right (by linarith [hbgt1]) (by norm_num)
    _ < b * |t| := mul_lt_mul_of_pos_left ht hb_pos

  have hbound_ball : ∀ s ∈ closedBall (3/2 + I * t) R, ‖riemannZeta s‖ < b * |t| := by
    have hsubset : closedBall (3/2 + I * t) R ⊆ closedBall (3/2 + I * t) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1)
    intro s hs
    have hs1 : s ∈ closedBall (3/2 + I * t) 1 := hsubset hs
    have ht2 : |t| > 2 := by linarith [ht]
    specialize hb t ht2
    exact hb s hs1

  have hexp := hexp_lemma (b * |t|) hBgt1 hbound_ball hfin z hz

  have hζne : riemannZeta (3/2 + I * t) ≠ 0 := zetacnot0 t
  have hζpos : (0 : ℝ) < ‖riemannZeta (3/2 + I * t)‖ := norm_pos_iff.mpr hζne

  have hBpos : (0 : ℝ) < b * |t| := mul_pos (by linarith [hbgt1]) htpos
  have hBne : b * |t| ≠ 0 := ne_of_gt hBpos
  have htne : |t| ≠ 0 := ne_of_gt htpos
  have hbne : b ≠ 0 := ne_of_gt (by linarith [hbgt1])

  have hlog_bound : Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) ≤
                    Real.log |t| + Real.log b + A := by
    rw [Real.log_div hBne (ne_of_gt hζpos)]
    rw [Real.log_mul hbne htne]
                                  
    have hA_bound := hA t
    have : -Real.log ‖riemannZeta (3/2 + I * t)‖ ≤ A := by
      have eq_neg : Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) = -Real.log ‖riemannZeta (3/2 + I * t)‖ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hζpos)]
        simp
      rw [← eq_neg]
      exact hA_bound
    linarith

  have hcoeff_nonneg : (0 : ℝ) ≤ 16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) := by
    apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · apply sq_nonneg
      · apply le_of_lt
        apply pow_pos
        linarith [hr1_lt_r]
    · apply div_nonneg
      · norm_num
      · apply le_of_lt
        apply mul_pos
        ·                          
          have h_gt : R > R1 := hR1_lt_R
          have h1_pos : (1 : ℝ) < R/R1 := by
            rw [one_lt_div]
            · exact h_gt
            · exact hR1_pos
          have h_sq_div : R^2/R1 = R * (R/R1) := by
            field_simp [ne_of_gt hR1_pos]
          rw [h_sq_div]
          have h_r_pos : (0 : ℝ) < R := by linarith [hR1_pos, h_gt]
          have : R * (R/R1) > R * 1 := by
            apply mul_lt_mul_of_pos_left h1_pos h_r_pos
          simp at this
          linarith [this]
        · apply Real.log_pos
          rw [one_lt_div]
          · exact hR1_lt_R
          · exact hR1_pos

  calc ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
      ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) := hexp
    _ ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
      exact mul_le_mul_of_nonneg_left hlog_bound hcoeff_nonneg

lemma helper_log_ratio_le_sum (b t x A : ℝ)
  (hb : b > 1) (ht : 0 < |t|) (hx : 0 < x) (hA : Real.log (1 / x) ≤ A) :
  Real.log ((b * |t|) / x) ≤ Real.log |t| + Real.log b + A := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have ht_ne : |t| ≠ 0 := ne_of_gt ht
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_inv_ne : (1 / x) ≠ 0 := one_div_ne_zero hx_ne
  calc
    Real.log ((b * |t|) / x)
        = Real.log ((b * |t|) * (1 / x)) := by simp [div_eq_mul_inv]
    _ = Real.log (b * |t|) + Real.log (1 / x) := by
      exact Real.log_mul (mul_ne_zero hb_ne ht_ne) h_inv_ne
    _ ≤ Real.log (b * |t|) + A := by
      exact add_le_add_right hA (Real.log (b * |t|))
    _ = Real.log b + Real.log |t| + A := by
      have hmul : Real.log (b * |t|) = Real.log b + Real.log |t| :=
    Real.log_mul hb_ne ht_ne
      simp [hmul, add_comm]
    _ = Real.log |t| + Real.log b + A := by
          simp [add_comm]

lemma helper_bound_sum_by_Klog (t b A : ℝ)
  (ht : |t| > 3) (hb : b > 1) (hA : A > 1) :
  ∃ K > 1, Real.log |t| + Real.log b + A ≤ K * Real.log (|t| + 2) := by
                   
  let S := Real.log b + A
  let K := 1 + S / Real.log 5
  have hpos_t : 0 < |t| := lt_trans (by norm_num) ht
                                                 
  have hle_log : Real.log |t| ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log
    · exact hpos_t
    · have hxle : |t| ≤ |t| + 2 := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        linarith
      exact hxle
                        
  have log5pos : 0 < Real.log (5 : ℝ) := by
    have : (1 : ℝ) < 5 := by norm_num
    exact Real.log_pos this
  have Spos : 0 < S := by
    have hlogbpos : 0 < Real.log b := Real.log_pos hb
    have hApos : 0 < A := lt_trans (by norm_num) hA
    exact add_pos hlogbpos hApos
  have Kgt1 : 1 < K := by
    have : 0 < S / Real.log 5 := div_pos Spos log5pos
    simpa [K] using (lt_add_of_pos_right (1 : ℝ) this)
                                           
  have hlog5_le : Real.log 5 ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log
    · exact (by norm_num : 0 < (5 : ℝ))
    · have : (5 : ℝ) < |t| + 2 := by linarith [ht]
      exact le_of_lt this
  have hfac_nonneg : 0 ≤ S / Real.log 5 := le_of_lt (div_pos Spos log5pos)
  have hmul : (S / Real.log 5) * Real.log 5 ≤ (S / Real.log 5) * Real.log (|t| + 2) :=
    mul_le_mul_of_nonneg_left hlog5_le hfac_nonneg
  have hleft : (S / Real.log 5) * Real.log 5 = S := by
    have hne : (Real.log 5) ≠ 0 := ne_of_gt log5pos
    field_simp [hne]
  have hS_le : S ≤ (S / Real.log 5) * Real.log (|t| + 2) := by
    simp [hleft] at hmul
    exact hmul
                         
  refine ⟨K, Kgt1, ?_⟩
  calc
    Real.log |t| + Real.log b + A
        = Real.log |t| + S := by
          simp [S, add_comm, add_left_comm]
    _
      ≤ Real.log (|t| + 2) + S := by
      exact add_le_add_left hle_log S
    _
      ≤ Real.log (|t| + 2) + (S / Real.log 5) * Real.log (|t| + 2) := by
      exact add_le_add_right hS_le (Real.log (|t| + 2))
    _ = (1 + S / Real.log 5) * Real.log (|t| + 2) := by
      ring
    _ = K * Real.log (|t| + 2) := by rfl
    _ = K * Real.log (|t| + 2) := by rfl

lemma Zeta1_Zeta_Expansion
    (r1 r : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < 5 / (6 : ℝ)) :
    ∃ C > 1,
    ∀ (t : ℝ) (_ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc (5 / (6 : ℝ)) c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      C * (1 / (r - r1)^3 + 1) * Real.log |t| := by
                                                             
  obtain ⟨A, hAgt1, b, hbgt1, hmain⟩ := Zeta1_Zeta_Expand
                      
  let R1 : ℝ := 5 / 6
  let R  : ℝ := 8 / 9
  have hR1_pos : 0 < R1 := by norm_num [R1]
  have hR1_lt_R : R1 < R := by norm_num [R1, R]
  have hR_lt_1  : R < 1 := by norm_num [R]
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
                                    
  let d : ℝ := (r - r1) ^ 3
  have hd_pos : 0 < d := by
    have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
    simpa [d] using pow_pos this 3
  let A0 : ℝ := 1 / ((R^2 / R1 - R1) * Real.log (R / R1))
  have hA0_pos : 0 < A0 := by
    have hx1 : 0 < R^2 / R1 - R1 := by
                                              
      norm_num [R, R1]
    have hx2 : 0 < Real.log (R / R1) := by
                         
      have : (1 : ℝ) < R / R1 := by norm_num [R, R1]
      exact Real.log_pos this
    have hxden : 0 < (R^2 / R1 - R1) * Real.log (R / R1) := mul_pos hx1 hx2
    simpa [A0] using (one_div_pos.mpr hxden)
                                                               
  let K : ℝ := 16 * r^2 / d + A0
                              
  let S : ℝ := Real.log b + A
  have hS_pos : 0 < S := by
    have hbpos : 0 < Real.log b := Real.log_pos hbgt1
    have hApos : 0 < A := lt_trans (by norm_num) hAgt1
    exact add_pos hbpos hApos
                                                                                          
  let Kcoeff : ℝ := max (16 * r^2) A0
  have hK_le : K ≤ Kcoeff * (1 / d + 1) := by
    have hx_nonneg : 0 ≤ 1 / d := by
      exact le_of_lt (one_div_pos.mpr hd_pos)
    have hα_le : 16 * r^2 / d ≤ Kcoeff * (1 / d) := by
        have hα : 16 * r^2 ≤ Kcoeff := le_max_left _ _
        have : (16 * r^2) * (1 / d) ≤ Kcoeff * (1 / d) :=
          mul_le_mul_of_nonneg_right hα hx_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hβ_le : A0 ≤ Kcoeff * 1 := by
      have hβ : A0 ≤ Kcoeff := le_max_right _ _
      simpa using hβ
    have : 16 * r^2 / d + A0 ≤ Kcoeff * (1 / d) + Kcoeff * 1 :=
      add_le_add hα_le hβ_le
    simpa [K, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using this
                                                  
  let C : ℝ := max (Kcoeff * (1 + S / Real.log 3)) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
                                                          
  intro t ht
                                         
  simp only
  intro hfin z hz
                                                
  have ht2 : |t| > 2 := by linarith [ht]
  have hineq0 :=
    hmain t ht2 r1 r R1 R hr1_pos hr1_lt_r (lt_trans hr1_pos hr1_lt_r) hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
  have hineq1 := hineq0 hfin z hz
                                 
  have hK_eq : (16 * r^2 / (r - r1)^3 + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) = K := by
    simp [K, A0, d, R1, R]
  have hLS_eq : Real.log |t| + Real.log b + A = Real.log |t| + S := by
    simp [S, add_comm, add_assoc]
  have hineq2 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * (Real.log |t| + S) := by
    rw [← hK_eq, ← hLS_eq]
    exact hineq1
                                                             
  have hlog3pos : 0 < Real.log (3 : ℝ) := by
    have : (1 : ℝ) < 3 := by norm_num
    exact Real.log_pos this
                                           
  have hpos_t : 0 < |t| := lt_trans (by norm_num) ht
  have hL_ge_log3' : Real.log 3 ≤ Real.log |t| := by
    have hge : (3 : ℝ) ≤ |t| := le_of_lt ht
    exact Real.log_le_log (by norm_num) hge
  have hratio_nonneg : 0 ≤ S / Real.log 3 := le_of_lt (div_pos hS_pos hlog3pos)
  have hneq : Real.log 3 ≠ 0 := ne_of_gt hlog3pos

  have hS_le : S ≤ (S / Real.log 3) * Real.log |t| := by

    calc S
      = (S / Real.log 3) * Real.log 3 := by simp [hneq]
      _ ≤ (S / Real.log 3) * Real.log |t| := mul_le_mul_of_nonneg_left hL_ge_log3' hratio_nonneg

  have hsum_bound : Real.log |t| + S ≤ (1 + S / Real.log 3) * Real.log |t| := by
    have hstep : Real.log |t| + S ≤ Real.log |t| + (S / Real.log 3) * Real.log |t| :=
      add_le_add_right hS_le (Real.log |t|)
                                                                                           
    have h_factor : Real.log |t| + (S / Real.log 3) * Real.log |t| = (1 + S / Real.log 3) * Real.log |t| := by ring
    rw [← h_factor]
    exact hstep
                                      
  have hineq3 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * ((1 + S / Real.log 3) * Real.log |t|) :=
    le_trans hineq2 (mul_le_mul_of_nonneg_left hsum_bound (by
      have hr2_nonneg : 0 ≤ r^2 := by
        have : 0 ≤ r * r := mul_nonneg (le_of_lt hr_pos) (le_of_lt hr_pos)
        simpa [pow_two] using this
      have hterm1 : 0 ≤ 16 * r^2 / d :=
        div_nonneg (mul_nonneg (by norm_num) hr2_nonneg) (le_of_lt hd_pos)
      have : 0 ≤ K := add_nonneg hterm1 (le_of_lt hA0_pos)
      exact this))
                                    
  have hKcoeff : K * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|) :=
    mul_le_mul_of_nonneg_right hK_le (by
      have hLpos : 0 < Real.log |t| :=
        Real.log_pos (lt_trans (by norm_num) ht)
      have hcoef_pos : 0 < 1 + S / Real.log 3 :=
        add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt (div_pos hS_pos hlog3pos))
      have : 0 ≤ (1 + S / Real.log 3) * Real.log |t| :=
        le_of_lt (mul_pos hcoef_pos hLpos)
      simpa using this)
                                                                     
  have hfinal := le_trans hineq3 hKcoeff
                                                    
  have hC_ge : Kcoeff * (1 + S / Real.log 3) ≤ C := by
    exact le_max_left _ _
                                           
  have : (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ C * (1 / d + 1) * Real.log |t| := by
    have hnonneg_term : 0 ≤ (1 / d + 1) * Real.log |t| := by
      have h1 : 0 ≤ 1 / d := le_of_lt (one_div_pos.mpr hd_pos)
      have h2 : 0 ≤ Real.log |t| := le_of_lt (Real.log_pos (lt_trans (by norm_num) ht))
      have : 0 ≤ (1 / d + 1) := add_nonneg h1 (by norm_num)
      exact mul_nonneg this h2
    have hstep := mul_le_mul_of_nonneg_left hC_ge hnonneg_term
                                         
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
                                                    
  have hfinal_le := le_trans hfinal this
  simp only [d] at hfinal_le
  exact hfinal_le

end Erdos970
