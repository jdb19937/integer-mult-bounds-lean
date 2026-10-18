module

public import IntegerMultBounds.Vendor.StrongPNT.PNT3_RiemannZeta
public import IntegerMultBounds.Vendor.StrongPNT.Z0

@[expose] public section

namespace Erdos970


def zeroZ : Set ℂ := {s : ℂ | riemannZeta s = 0}

def ZetaZerosNearPoint (t : ℝ) : Set ℂ := { ρ : ℂ | ρ ∈ zeroZ ∧ ‖ρ - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) }

lemma ZetaZerosNearPoint_finite (t : ℝ) : Set.Finite (ZetaZerosNearPoint t) := by
                                  
  let c : ℂ := (3/2 : ℂ) + t * Complex.I
  let R : ℝ := (5/6 : ℝ)
  have hRpos : 0 < R := by norm_num

  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  have hH_diff : Differentiable ℂ H := by
                                                               
    intro s
    rcases eq_or_ne s 1 with rfl | hs
    ·                                                                                                
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                             
        filter_upwards [self_mem_nhdsWithin] with t ht
                                                                              
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                           
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) s := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) s :=
          (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta s :=
          (differentiableAt_riemannZeta hs)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hs] with u hu using by
        simp [H, Function.update_of_ne hu]

  by_cases hPoleIn : ‖1 - c‖ ≤ R
  ·                                                         
    let g : ℂ → ℂ := fun z => H (z + c)
                                                                                                   
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
                                     
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
                                                             
      exact riemannZeta_ne_zero_of_one_le_re (by
                        
        have : (1 : ℝ) < c.re := hgt
        exact le_of_lt this)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
                                                           
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
                                                             
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr (by
                                 
        exact hcne1)) hzeta_c_ne
                                                  
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                                                                        
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
                                          
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
                                                      
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
                                          
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by simp [hform, hzeroζ]
      exact ⟨hball, hzero'⟩
                                                                                                 
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
                                        
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
                                                                    
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
                                                                                    
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
                                                
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset
  ·                                             
    let g : ℂ → ℂ := fun z => H (z + c)
                                          
    have hzeta_c_ne : riemannZeta c ≠ 0 := by
      have : c.re = (3/2 : ℝ) := by
        simp [c, Complex.add_re, Complex.mul_re, Complex.I_re]
      have hgt : c.re > 1 := by simpa [this] using (by norm_num : (3:ℝ)/2 > 1)
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hgt)
    have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := by
      have h0in : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hRpos
      refine ⟨0, h0in, ?_⟩
      have hcne1 : c ≠ (1 : ℂ) := by
        intro hc; have hcreq : c.re = 1 := by simp [hc, Complex.one_re]
        have : (3 : ℝ) / 2 = (1 : ℝ) := by
          simpa [c, Complex.add_re, Complex.mul_re, Complex.I_re] using hcreq
        norm_num at this
                                      
      have hHc : g 0 = H c := by simp [g]
      have : g 0 = (c - 1) * riemannZeta c := by
        simpa [H, Function.update_of_ne hcne1] using hHc
      simpa [this] using mul_ne_zero (sub_ne_zero.mpr hcne1) hzeta_c_ne
                                          
    let Kg : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ g ρ = 0}
                     
    have h_subset : ZetaZerosNearPoint t ⊆ {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      intro ρ hρ
      rcases hρ with ⟨hzero, hdist⟩
      have hball : ρ - c ∈ Metric.closedBall 0 R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, c, sub_eq_add_neg] using hdist
      have hρne1 : (ρ : ℂ) ≠ 1 := by
        intro hρ1
        have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
        exact hz1_ne (by simpa [hρ1] using! hzero)
      have hsum : (ρ - c) + c = ρ := by simp [sub_add_cancel]
      have hxne : (ρ - c) + c ≠ (1 : ℂ) := by simpa [hsum] using hρne1
      have hform : g (ρ - c) = (ρ - 1) * riemannZeta ρ := by
        simp [g, H, hsum, Function.update_of_ne hxne]
                                                   
      have hzeroζ : riemannZeta ρ = 0 := hzero
      have hzero' : g (ρ - c) = 0 := by
        calc
          g (ρ - c) = (ρ - 1) * riemannZeta ρ := hform
          _ = (ρ - 1) * 0 := by simp [hzeroζ]
          _ = 0 := by simp
      exact ⟨hball, hzero'⟩
                            
    have hg_diff : Differentiable ℂ g := by
      intro z
      have hH := hH_diff (z + c)
      have h_addc : DifferentiableAt ℂ (fun z : ℂ => z + c) z :=
        (differentiableAt_id.add_const c)
      simpa [g] using! hH.comp z h_addc
    have hg_analyticNhd_univ : AnalyticOnNhd ℂ g Set.univ :=
      (Complex.analyticOnNhd_univ_iff_differentiable).2 hg_diff
    have hg_analyticNhd : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
      AnalyticOnNhd.mono hg_analyticNhd_univ (by intro z hz; simp)
    have hNonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
      rcases hg_nonzero with ⟨z, hz_in, hz_ne⟩
      have hz_in' : z ∈ Metric.ball (0 : ℂ) 1 := by
        have hRle : (R : ℝ) ≤ 1 := by norm_num
        exact Metric.ball_subset_ball hRle hz_in
      exact ⟨z, hz_in', hz_ne⟩
    have hfiniteKg : Set.Finite Kg :=
      (lem_Contra_finiteKR R hRpos (by norm_num : R < 1) g hg_analyticNhd hNonzero)
    have hTarget_eq : {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} =
          (fun ρ : ℂ => ρ + c) '' Kg := by
      ext ρ; constructor
      · intro h
        rcases h with ⟨hball, hzero⟩
        refine ⟨ρ - c, ⟨?_, ?_⟩, ?_⟩
        · exact hball
        · exact hzero
        · simp [sub_add_cancel]
      · intro h
        rcases h with ⟨z, ⟨hzball, hz0⟩, rfl⟩
        constructor
        · simpa [sub_add_cancel] using hzball
        · simpa [sub_add_cancel] using hz0
    have hTarget_fin : Set.Finite {ρ : ℂ | (ρ - c) ∈ Metric.closedBall 0 R ∧ g (ρ - c) = 0} := by
      have himg : Set.Finite ((fun ρ : ℂ => ρ + c) '' Kg) := hfiniteKg.image _
      exact hTarget_eq ▸ himg
    exact Set.Finite.subset hTarget_fin h_subset

lemma lem_Re1zge0 (z : ℂ) : z.re > 0 → (1 / z).re > 0 := by
  intro h
                          
  have hz_ne_zero : z ≠ 0 := by
    intro hz_eq_zero
    rw [hz_eq_zero] at h
    simp at h
                                
  rw [one_div]
                                               
  rw [Complex.inv_re]
                                                                                                     
  apply div_pos h
                             
  rwa [Complex.normSq_pos]

lemma lem_sigmage1 (sigma t : ℝ) (hsigma : sigma > 1) : riemannZeta (sigma + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.I_re]
  linarith

lemma lem_sigmale1 (sigma1 t1 : ℝ) : riemannZeta (sigma1 + t1 * Complex.I) = 0 → sigma1 ≤ 1 := by
  intro h
                                       
  by_contra h_not_le
                                                   
  push Not at h_not_le
                                                                             
  have h_nonzero := lem_sigmage1 sigma1 t1 h_not_le
                                                              
  exact h_nonzero h

lemma lem_sigmale1Zt (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) : rho1.re ≤ 1 := by
                                                                    
  have h1 : rho1 ∈ zeroZ := h_rho1_in_Zt.1
                                                                  
  have h2 : riemannZeta rho1 = 0 := h1
                                                       
  have h3 : rho1 = rho1.re + rho1.im * Complex.I := by simp [Complex.re_add_im]
                                         
  rw [h3] at h2
                           
  exact lem_sigmale1 rho1.re rho1.im h2

lemma lem_s_notin_Zt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
  ((1 : ℂ) + δ + t * Complex.I) ∉ ZetaZerosNearPoint t := by
  intro hmem
                                                    
  have h_zero : riemannZeta ((1 : ℂ) + δ + t * Complex.I) = 0 := hmem.1
                                              
  have h_gt : (1 : ℝ) + δ > 1 := by linarith [hδ]
  have h_nonzero := lem_sigmage1 (1 + δ) t h_gt
                                                          
  have h_coercion : (1 : ℂ) + δ = ↑(1 + δ) := by simp [Complex.ofReal_add]
                                  
  rw [h_coercion] at h_zero
  exact h_nonzero h_zero

lemma complex_abs_of_real (x : ℝ) : ‖(x : ℂ)‖ = abs x := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma complex_add_real_imag_parts (a b : ℝ) (t : ℝ) :
  ((a : ℂ) + b + t * Complex.I).re = a + b ∧ ((a : ℂ) + b + t * Complex.I).im = t := by
  constructor
                                 
  · rw [Complex.add_re, Complex.add_re]
                                                                       
    simp [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
                                      
  · rw [Complex.add_im, Complex.add_im]
                                                                   
    simp [Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]

lemma complex_abs_real_cast (r : ℝ) : ‖(r : ℂ)‖ = abs r := Complex.norm_real r

lemma isBigO_comp_principal_domain {α β E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  {f : β → E} {g : β → F} {h : α → β} {l : Filter α} {s : Set β}
  (hfg : f =O[Filter.principal s] g)
  (h_domain : ∀ᶠ x in l, h x ∈ s) :
  (f ∘ h) =O[l] (g ∘ h) := by
                                                             
  have h_le : Filter.map h l ≤ Filter.principal s := by
    intro t ht
                                                     
    rw [Filter.mem_principal] at ht
                                                                 
    rw [Filter.mem_map]
                                              
    rw [Filter.eventually_iff] at h_domain
                                                         
    apply Filter.mem_of_superset h_domain
    intro x hx
    exact ht hx

  have hfg_map : f =O[Filter.map h l] g := Asymptotics.IsBigO.mono hfg h_le

  rwa [Asymptotics.isBigO_map] at hfg_map

lemma isBigOWith_comp_principal_domain {α β E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  {C : ℝ} {f : β → E} {g : β → F} {h : α → β} {l : Filter α} {s : Set β}
  (hfg : Asymptotics.IsBigOWith C (Filter.principal s) f g)
  (h_domain : ∀ᶠ x in l, h x ∈ s) :
  Asymptotics.IsBigOWith C l (f ∘ h) (g ∘ h) := by
                                                                                             
  rw [Asymptotics.isBigOWith_iff, Filter.eventually_principal] at hfg
                                                        
  rw [Asymptotics.isBigOWith_iff]
                                          
  filter_upwards [h_domain] with x hx_in_s
                                                                       
  exact hfg (h x) hx_in_s

lemma s_in_D12 (delta : ℝ) (hdelta_pos : 0 < delta) (t : ℝ) (hdelta_lt : delta < 1) :
  ((1 : ℂ) + (delta : ℝ) + (t : ℝ) * Complex.I) ∈
    Metric.ball ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) (1 / 2) := by
                                                       
  rw [Metric.mem_ball]
                             
  have h1 : ((1 : ℂ) + (delta : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) =
            (1 : ℂ) + (delta : ℝ) - (3 / 2 : ℂ) := by ring
                                
  have h2 : (1 : ℂ) + (delta : ℝ) - (3 / 2 : ℂ) = (delta - 1/2 : ℝ) := by
    simp [Complex.ofReal_sub]
    ring
                                                            
  rw [Complex.dist_eq, h1, h2, Complex.norm_real]
                                    
  rw [Real.norm_eq_abs]
                                                           
  have h3 : abs (delta - 1/2) < 1/2 := by
    rw [abs_lt]
    constructor
    ·                                       
      linarith [hdelta_pos]
    ·                                      
      linarith [hdelta_lt]
  exact h3

lemma zerosetKfRc_eq_ZetaZerosNearPoint (t : ℝ) :
  zerosetKfRc (5/6 : ℝ) ((3/2 : ℂ) + t * Complex.I) riemannZeta = ZetaZerosNearPoint t := by
  ext ρ; constructor
  · intro h
    rcases h with ⟨hball, hzero⟩
    refine ⟨?hz, ?hnorm⟩
    · simpa [zeroZ] using hzero
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hball
  · intro h
    rcases h with ⟨hz, hnorm⟩
    refine ⟨?hball, ?hzero⟩
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hnorm
    · simpa [zeroZ] using hz

lemma mem_closedBall_of_mem_ball {x c : ℂ} {r : ℝ} (hx : x ∈ Metric.ball c r) :
  x ∈ Metric.closedBall c r := by
  exact (Metric.ball_subset_closedBall) hx

lemma I_mul_real_eq_real_mul_I (t : ℝ) :
  (Complex.I : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I := by
  simpa using mul_comm (Complex.I : ℂ) (t : ℂ)

lemma center_eq_comm (t : ℝ) :
  ((3/2 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ((3/2 : ℂ) + (t : ℂ) * Complex.I) := by
  have h : (Complex.I : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I := by
    simpa using mul_comm (Complex.I : ℂ) (t : ℂ)
  simp [h]

lemma log_abs_le_log_abs_add_two {t : ℝ} (ht : 2 < |t|) :
  Real.log (abs t) ≤ Real.log (abs t + 2) := by
  have hpos : 0 < |t| := lt_trans (by norm_num) ht
  have hle : |t| ≤ |t| + 2 := by nlinarith
  simpa using Real.log_le_log hpos hle

lemma s_notin_ZetaZerosNearPoint (δ t : ℝ) (hδ_pos : 0 < δ) :
  ((1 : ℂ) + δ + t * Complex.I) ∉ ZetaZerosNearPoint t := by
  intro hmem
  have hz0 : riemannZeta ((1 : ℂ) + δ + t * Complex.I) = 0 := hmem.1
  have : ((1 : ℂ) + δ + t * Complex.I).re = 1 + δ := by simp
  have hpos : (1 : ℝ) < 1 + δ := by linarith
  have hnonzero := lem_sigmage1 (1 + δ) t hpos
  exact hnonzero (by simpa using hz0)

lemma norm_sub_comm' (x y : ℂ) : ‖x - y‖ = ‖y - x‖ := by
  calc
    ‖x - y‖ = ‖-(x - y)‖ := by simpa using (norm_neg (x - y)).symm
    _ = ‖y - x‖ := by simp [neg_sub]

lemma s_in_closedBall_12 (δ t : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
  ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) ∈
    Metric.closedBall ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) (1 / 2) := by
                                         
  have hdiff :
      ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)
        = ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) := by
    simp
  have hreal :
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) = ((δ - (1 / 2 : ℝ)) : ℂ) := by
    have h' : ((1 + δ : ℝ) - (3 / 2 : ℝ)) = δ - (1 / 2 : ℝ) := by
      calc
        (1 + δ) - (3 / 2 : ℝ) = δ + 1 - (3 / 2 : ℝ) := by ac_rfl
        _ = δ + (1 - (3 / 2 : ℝ)) := by simp [add_sub_assoc]
        _ = δ + (- (1 / 2 : ℝ)) := by norm_num
        _ = δ - (1 / 2 : ℝ) := by simp [sub_eq_add_neg]
    calc
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)
          = ((1 + δ : ℝ) : ℂ) - (3 / 2 : ℂ) := by
              simp [add_comm]
      _ = (↑((1 + δ : ℝ) - (3 / 2 : ℝ)) : ℂ) := by
              simp [Complex.ofReal_sub]
      _ = ((δ - (1 / 2 : ℝ)) : ℂ) := by simp [h']
  have hnormle :
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (1 / 2 : ℝ) := by
    calc
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
          = ‖((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)‖ := by simp [hdiff]
      _ = ‖((δ - (1 / 2 : ℝ)) : ℂ)‖ := by simp [hreal]
      _ = |δ - (1 / 2 : ℝ)| := by simpa using complex_abs_real_cast (δ - (1 / 2 : ℝ))
      _ ≤ 1 / 2 := by
        have hleft : - (1 / 2 : ℝ) ≤ δ - 1 / 2 := by linarith [hδ_pos]
        have hright : δ - 1 / 2 ≤ 1 / 2 := by linarith [hδ_lt]
        simpa using (abs_le.mpr ⟨hleft, hright⟩)
                                           
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hnormle

lemma lem_explicit1deltat :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
                  (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))
                - logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)‖
          ≤ C * Real.log (abs t + 2) := by
  classical
                               
  let r1 : ℝ := (1/2 : ℝ)
  let r  : ℝ := (2/3 : ℝ)
  let R1 : ℝ := (5/6 : ℝ)
  let R  : ℝ := (9/10 : ℝ)
  have hr1_pos : 0 < r1 := by norm_num
  have hr_pos  : 0 < r := by norm_num
  have hr1_lt_r : r1 < r := by norm_num
  have hr_lt_R1 : r < R1 := by norm_num
  have hR1_pos : 0 < R1 := by norm_num
  have hR1_lt_R : R1 < R := by norm_num
  have hR_lt_1  : R < 1 := by norm_num
                     
  let F : ℝ := (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)))
                       
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨A, hA_gt1, hA_bound⟩ := zeta32lower_log
                                                      
  let K : ℝ := 1 + (Real.log b + A) / Real.log 4
                   
  let C : ℝ := max (F * K) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
                             
  intro t ht δ hδ
  rcases hδ with ⟨hδ_pos, hδ_lt1⟩
                                 
  let c_std : ℂ := ((3/2 : ℂ) + Complex.I * (t : ℂ))
  let c_comm : ℂ := ((3/2 : ℂ) + (t : ℝ) * Complex.I)
  have hcenter_eq : c_std = c_comm := by simpa [c_std, c_comm] using (center_eq_comm t)
  let s : ℂ := (1 : ℂ) + δ + t * Complex.I
                            
  have hs_mem_comm : s ∈ Metric.closedBall c_comm r1 := s_in_closedBall_12 δ t hδ_pos hδ_lt1
  have hs_mem_std : s ∈ Metric.closedBall c_std r1 := by simpa [c_std, c_comm, hcenter_eq] using hs_mem_comm
                 
  have hs_notin_Zt : s ∉ ZetaZerosNearPoint t := s_notin_ZetaZerosNearPoint δ t hδ_pos
  have hzeros_eq : zerosetKfRc (5/6 : ℝ) c_comm riemannZeta = ZetaZerosNearPoint t := by
    simpa [c_comm] using zerosetKfRc_eq_ZetaZerosNearPoint t
  have hs_notin_comm : s ∉ zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by simpa [hzeros_eq] using hs_notin_Zt
  have hs_notin_std : s ∉ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [c_std, c_comm, hcenter_eq] using hs_notin_comm
                    
  have hfin_comm : (zerosetKfRc (5/6 : ℝ) c_comm riemannZeta).Finite := by
    simpa [hzeros_eq] using (ZetaZerosNearPoint_finite t)
  have hfin_std : (zerosetKfRc (5/6 : ℝ) c_std riemannZeta).Finite := by
    simpa [c_std, c_comm, hcenter_eq] using hfin_comm
                                                         
  have h_bound_R : ∀ z ∈ Metric.closedBall c_std R, ‖riemannZeta z‖ < b * |t| := by
    intro z hz
    have hsubs : Metric.closedBall c_std R ⊆ Metric.closedBall c_std (1 : ℝ) := by
      intro w hw; exact Metric.closedBall_subset_closedBall (by norm_num : (R : ℝ) ≤ (1 : ℝ)) hw
    exact hb_bound t (by simpa using ht) z (hsubs hz)
                                  
  have hmain :=
    log_Deriv_Expansion_Zeta t ht
      r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
                    
  have hbpos : 0 < b := lt_trans (by norm_num) hb_gt1
  have ht1 : 1 < |t| := lt_trans (by norm_num) ht
  have hmul : b * 1 < b * |t| := (mul_lt_mul_of_pos_left ht1 hbpos)
  have hB_gt1 : 1 < b * |t| := lt_trans hb_gt1 (by simpa using hmul)
  have hineq := hmain (b * |t|) hB_gt1 h_bound_R
  have hz_in : s ∈ Metric.closedBall c_std r1 \ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := ⟨hs_mem_std, hs_notin_std⟩
  have hineq2 := hineq hfin_std s hz_in
                                                           
  have hFinset_eq : hfin_std.toFinset = (ZetaZerosNearPoint_finite t).toFinset := by
    ext ρ; constructor <;> intro hρ
    · have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [Set.mem_toFinset] using hρ
      have : ρ ∈ ZetaZerosNearPoint t := by
        have heq : zerosetKfRc (5/6 : ℝ) c_std riemannZeta = zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by
                                                                                    
          simp [c_std, c_comm, hcenter_eq]
        simpa [hzeros_eq, heq]
          using this
      simpa [Set.mem_toFinset] using this
    · have : ρ ∈ ZetaZerosNearPoint t := by simpa [Set.mem_toFinset] using hρ
      have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by simpa [hzeros_eq] using this
      have heq : zerosetKfRc (5/6 : ℝ) c_std riemannZeta = zerosetKfRc (5/6 : ℝ) c_comm riemannZeta := by
        simp [c_std, c_comm, hcenter_eq]
      have : ρ ∈ zerosetKfRc (5/6 : ℝ) c_std riemannZeta := by simpa [heq] using this
      simpa [Set.mem_toFinset] using this
  have hLHS_le :
      ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
            (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1))
          - logDerivZeta s‖
      ≤ F * Real.log (b * |t| / ‖riemannZeta c_std‖) := by
    have :
        ‖logDerivZeta s -
            Finset.sum (hfin_std.toFinset)
              (fun ρ : ℂ => ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖
        ≤ F * Real.log (b * |t| / ‖riemannZeta c_std‖) := by
      simpa [F] using! hineq2
    simpa [norm_sub_comm', hFinset_eq]
      using this
                                   
  have hc_ne : riemannZeta c_std ≠ 0 := by simpa [c_std] using! zetacnot0 t
  have hnorm_pos : 0 < ‖riemannZeta c_std‖ := by simpa [norm_pos_iff] using hc_ne
  have hnorm_ne : ‖riemannZeta c_std‖ ≠ 0 := ne_of_gt hnorm_pos
  have hb_ne : b ≠ 0 := ne_of_gt hbpos
  have htpos0 : 0 < |t| := lt_trans (by norm_num) ht
  have ht_ne : |t| ≠ 0 := ne_of_gt htpos0
  have hlog_mul1 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        = Real.log (b * |t|) + Real.log (1 / ‖riemannZeta c_std‖) := by
    simpa [div_eq_mul_inv] using Real.log_mul (mul_ne_zero hb_ne ht_ne) (inv_ne_zero hnorm_ne)
  have hlog_mul2 : Real.log (b * |t|) = Real.log b + Real.log (|t|) := by
    simpa using Real.log_mul hb_ne ht_ne
  have hζ_log_le : Real.log (1 / ‖riemannZeta c_std‖) ≤ A := by
    simpa [c_std] using! hA_bound t
  have hlog_bound1 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ (Real.log b + Real.log (|t|)) + A := by
    have := add_le_add_right hζ_log_le (Real.log (b * |t|))
    simpa [hlog_mul1, hlog_mul2, add_comm, add_left_comm, add_assoc] using this
                                    
  have hlog_mono : Real.log (|t|) ≤ Real.log (|t| + 2) :=
    log_abs_le_log_abs_add_two (by simpa using ht)
  have hlog_bound2 :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ Real.log (|t| + 2) + (Real.log b + A) := by
    have : Real.log b + Real.log (|t|) + A ≤ Real.log b + Real.log (|t| + 2) + A := by
      have := add_le_add_right hlog_mono (Real.log b)
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left this A
    exact le_trans hlog_bound1 (by simpa [add_comm, add_left_comm, add_assoc] using this)
                                                
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hge5 : Real.log 4 ≤ Real.log (|t| + 2) := by
    have hxy : (4 : ℝ) ≤ |t| + 2 := by nlinarith [le_of_lt ht]
    exact Real.log_le_log (by norm_num) hxy
  have hconst_nonneg : 0 ≤ Real.log b + A := by
    have hbposlog : 0 < Real.log b := Real.log_pos hb_gt1
    have hApos : 0 < A := lt_trans (by norm_num) hA_gt1
    have : 0 ≤ Real.log b := le_of_lt hbposlog
    nlinarith
  have hnonneg : 0 ≤ (Real.log b + A) / Real.log 4 := div_nonneg hconst_nonneg (le_of_lt hlog5pos)
  have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
  have hconst_bound : (Real.log b + A)
        ≤ (Real.log b + A) / Real.log 4 * Real.log (|t| + 2) := by
    have := mul_le_mul_of_nonneg_left hge5 hnonneg
                             
    have : ((Real.log b + A) / Real.log 4) * Real.log 4 ≤ (Real.log b + A) / Real.log 4 * Real.log (|t| + 2) := this
                                        
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne5] using this
  have hlog_bound3 :
      Real.log (|t| + 2) + (Real.log b + A)
        ≤ K * Real.log (|t| + 2) := by
    have := add_le_add_right hconst_bound (Real.log (|t| + 2))

    simpa [K, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, one_mul]
      using this
  have hlog_bound_final :
      Real.log (b * |t| / ‖riemannZeta c_std‖)
        ≤ K * Real.log (|t| + 2) := le_trans hlog_bound2 hlog_bound3
               
  have hF_nonneg : 0 ≤ F := by
    have h1 : 0 ≤ 16 * r ^ 2 / (r - r1) ^ 3 := by
      have hnum : 0 ≤ 16 * r ^ 2 := by
        have : 0 ≤ (16 : ℝ) := by norm_num
        have : 0 ≤ r ^ 2 := by
          have := sq_nonneg r
          simpa [pow_two] using this
        simpa [mul_comm] using mul_nonneg (show 0 ≤ (16 : ℝ) by norm_num) this
      have hden : 0 < (r - r1) ^ 3 := by
        have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
        simpa using pow_pos this 3
      exact div_nonneg hnum (le_of_lt hden)
    have h2 : 0 ≤ 1 / ((R ^ 2 / R1 - R1) * Real.log (R / R1)) := by
                           
      have hden1 : 0 < (R ^ 2 / R1 - R1) := by
        change 0 < ((9/10 : ℝ) ^ 2 / (5/6 : ℝ) - (5/6 : ℝ))
        norm_num
      have hden2 : 0 < Real.log (R / R1) := by
        have : 1 < R / R1 := by
          change (1 : ℝ) < (9/10 : ℝ) / (5/6 : ℝ)
          norm_num
        exact Real.log_pos this
      have hpos : 0 < ((R ^ 2 / R1 - R1) * Real.log (R / R1)) := mul_pos hden1 hden2
      exact le_of_lt (one_div_pos.mpr hpos)
    have := add_nonneg h1 h2
    simpa [F] using this
                                       
  have hY_nonneg : 0 ≤ Real.log (|t| + 2) := by
                            
    have hgt1 : (1 : ℝ) < |t| + 2 := by
      have : (2 : ℝ) ≤ |t| + 2 := by
        have : 0 ≤ |t| := abs_nonneg t
        simp
      exact lt_of_lt_of_le (by norm_num) this
    exact le_of_lt (Real.log_pos hgt1)
  have hfinal1 :
      ‖Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
            (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1))
          - logDerivZeta s‖
      ≤ F * (K * Real.log (|t| + 2)) :=
    le_trans hLHS_le (by exact mul_le_mul_of_nonneg_left hlog_bound_final hF_nonneg)
  have hFactor_leC : F * K ≤ C := by exact le_trans (le_of_eq rfl) (le_max_left _ _)
  have hfinal2 : F * (K * Real.log (|t| + 2)) ≤ C * Real.log (|t| + 2) := by
    have := mul_le_mul_of_nonneg_right hFactor_leC hY_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have := le_trans hfinal1 hfinal2
  simpa [s]

lemma lem_explicit1RealReal :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          abs ((logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)).re
            - (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
                (fun rho1 : ℂ =>
                  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                    (((1 : ℂ) + δ + t * Complex.I) - rho1)).re)))
          ≤ C * Real.log (|t| + 2) := by
  rcases lem_explicit1deltat with ⟨C, hCpos, hE⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                  
  let s : ℂ := (1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I
  let S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  let g : ℂ → ℂ := fun rho1 : ℂ =>
    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (s - rho1)
                                           
  have ht' : ‖logDerivZeta s - ∑ rho1 ∈ S, g rho1‖
      ≤ C * Real.log (abs t + 2) := by
                                                 
    have h_app := hE t ht δ hδ
    rw [norm_sub_rev] at h_app
    exact h_app
                                
  have hleft_eq :
      abs ((logDerivZeta s).re - ∑ rho1 ∈ S, (g rho1).re)
        = abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re) := by
    simp [Complex.sub_re, Complex.re_sum]
                 
  have hbound :
      abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re)
        ≤ ‖logDerivZeta s - ∑ rho1 ∈ S, g rho1‖ := by
    simpa using Complex.abs_re_le_norm (logDerivZeta s - ∑ rho1 ∈ S, g rho1)
            
  have hfinal :
      abs ((logDerivZeta s - ∑ rho1 ∈ S, g rho1).re)
        ≤ C * Real.log (abs t + 2) :=
    le_trans hbound ht'
                                                      
  have hnorm : |t| = abs t := rfl
  simpa [s, S, g, hleft_eq, hnorm] using hfinal

lemma lem_explicit2Real :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          abs (
            (logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re
            - (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
                (fun rho1 : ℂ =>
                  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                    (((1 : ℂ) + δ + (2 * t) * Complex.I) - rho1)).re))
          )
          ≤ C * Real.log (abs (2 * t) + 2) := by
  rcases lem_explicit1RealReal with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                       
  have h_2t : 2 < |2 * t| := by
    rw [abs_mul, abs_two]
    linarith [ht]
  have h_bound := hEv (2 * t) h_2t δ hδ
                                 
  simp only [Complex.ofReal_mul] at h_bound
  exact h_bound

lemma lem_Realsum {α : Type*} (s : Finset α) (f : α → ℂ) : (Finset.sum s f).re = Finset.sum s (fun i => (f i).re) := by
  exact Complex.re_sum s f

lemma lem_Ztfinite (t : ℝ) : Set.Finite (ZetaZerosNearPoint t) := ZetaZerosNearPoint_finite t

lemma lem_sumrho1 (t : ℝ) (δ : ℝ) (_hdelta_pos : δ > 0) (_hdelta_lt1 : δ < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
        (fun rho1 : ℂ =>
                    ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
    (fun rho1 : ℂ =>
                    (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1)).re) := by
  exact lem_Realsum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) _

lemma lem_sumrho2 (t : ℝ) (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
        (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1))).re =
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
    (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1)).re) := by
  rw [Complex.re_sum]

lemma lem_1deltatrho1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (_h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1) = ((1 : ℝ) + delta - rho1.re) + (t - rho1.im) * Complex.I := by
                                                           
  conv_lhs => rw [← Complex.re_add_im rho1]

  simp only [sub_add_eq_sub_sub]
                                                      
  ring_nf
                                                               
  simp only [Complex.ofReal_one]
  ring

lemma lem_Re1deltatrho1 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re = (1 : ℝ) + delta - rho1.re := by
                                                   
  rw [lem_1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]

  rw [Complex.add_re]
                                      
  rw [Complex.mul_I_re]
             
  simp

lemma lem_Re1delta1 (delta : ℝ) (_hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 : ℝ) + delta - rho1.re ≥ delta := by
                                            
  have h_rho1_re_le_1 : rho1.re ≤ 1 := lem_sigmale1Zt t rho1 h_rho1_in_Zt
                               
  have h_nonneg : 1 - rho1.re ≥ 0 := by linarith
                                                                              
  linarith

lemma lem_Re1deltatge (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :    ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := by
                                                     
  rw [lem_Re1deltatrho1 delta hdelta t rho1 h_rho1_in_Zt]
                                                      
  exact lem_Re1delta1 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatneq0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
((1 : ℂ) + delta + t * Complex.I - rho1).re > 0 := by
                                                               
  have h_ge_delta : ((1 : ℂ) + delta + t * Complex.I - rho1).re ≥ delta := lem_Re1deltatge delta hdelta t rho1 h_rho1_in_Zt
                                                                         
  linarith [hdelta]

lemma lem_Re1deltatge0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 / ((1 : ℂ) + delta + t * Complex.I - rho1)).re ≥ 0 := by
                                                                      
  apply le_of_lt
  apply lem_Re1zge0
                                                          
  exact lem_Re1deltatneq0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1deltatge0m (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (_hdelta_lt_1 : delta < 1)
  (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
  (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
    (((1 : ℂ) + delta + t * Complex.I) - rho1)).re ≥ 0 := by
                                                     
  let n := (analyticOrderAt riemannZeta rho1).toNat
  let z := ((1 : ℂ) + delta + t * Complex.I) - rho1

  have h_eq : (n : ℂ) / z = n • (1/z) := by
    rw [nsmul_eq_mul]
    simp [div_eq_mul_inv]

  rw [h_eq, Complex.re_nsmul]

  apply nsmul_nonneg
  exact lem_Re1deltatge0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_Re1delta2tge0 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t)) :
(((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re ≥ 0 := by
                                                      
  convert lem_Re1deltatge0m delta hdelta (2 * t) hdelta_lt_1 rho1 h_rho1_in_Zt
  simp

lemma lem_sumrho2ge (t : ℝ) (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) :
Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t))) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re) ≥ 0 := by
  apply Finset.sum_nonneg
  intro rho1 h_rho1_in_finset
                                                                   
  have h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t) := by
    rwa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite (2 * t))] at h_rho1_in_finset
                            
  exact lem_Re1delta2tge0 delta hdelta hdelta_lt_1 t rho1 h_rho1_in_Zt

lemma lem_sumrho2ge02 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) :
    (Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)))
(fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1))).re ≥ 0 := by
                                                                                   
  rw [lem_sumrho2 t delta hdelta hdelta_lt_1]
                                                             
  exact lem_sumrho2ge t delta hdelta hdelta_lt_1

lemma lem_explicit2Real2 :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ((-logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re)
          ≤ C * Real.log (abs (2 * t) + 2) := by
  rcases lem_explicit2Real with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
                  
  set s : ℂ := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t))
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
          (s - rho1)).re)
                                                                  
  have h_bound :
      abs ((logDerivZeta s).re - Sre)
        ≤ C * Real.log (abs (2 * t) + 2) := by
    simpa [s, S, Sre] using hEv t ht δ hδ
                                                                     
  have hS_nonneg : 0 ≤ Sre := by
                                                                       
    have h0 := lem_sumrho2ge02 t δ hδ.1 hδ.2

    simpa [s, S, Sre, lem_sumrho2 t δ hδ.1 hδ.2] using h0
                                             
  have h_left : -(C * Real.log (abs (2 * t) + 2)) ≤ (logDerivZeta s).re - Sre :=
    (abs_le.mp h_bound).1
                                        
  have h_neg : -((logDerivZeta s).re - Sre) ≤ C * Real.log (abs (2 * t) + 2) := by
    simpa using neg_le_neg h_left
                                                                  
  have h_aux := sub_le_sub_right h_neg Sre
  have h_isol : - (logDerivZeta s).re ≤ C * Real.log (abs (2 * t) + 2) - Sre := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_aux
                                               
  have h_drop : C * Real.log (abs (2 * t) + 2) - Sre ≤ C * Real.log (abs (2 * t) + 2) :=
    sub_le_self _ hS_nonneg
             
  have h_final := le_trans h_isol h_drop
                                                            
  simpa [s, Complex.neg_re] using h_final

lemma lem_log2Olog : (fun t : ℝ => Real.log (2 * t)) =O[Filter.atTop] (fun t : ℝ => Real.log t) := by
                                                     
  have h_eq : (fun t : ℝ => Real.log (2 * t)) =ᶠ[Filter.atTop] (fun t : ℝ => Real.log 2 + Real.log t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht)]

  have h_bigO : (fun t : ℝ => Real.log 2 + Real.log t) =O[Filter.atTop] (fun t : ℝ => Real.log t) := by

    have h_const : (fun _ : ℝ => Real.log 2) =o[Filter.atTop] Real.log :=
      Real.isLittleO_const_log_atTop
    have h_self : Real.log =O[Filter.atTop] Real.log :=
      Asymptotics.isBigO_refl _ _
                             
    have h_const_bigO : (fun _ : ℝ => Real.log 2) =O[Filter.atTop] Real.log :=
      Asymptotics.IsLittleO.isBigO h_const
                                          
    exact Asymptotics.IsBigO.add h_const_bigO h_self

  exact h_eq.trans_isBigO h_bigO

lemma lem_w2t (t : ℝ) : abs (2 * t) + 2 ≥ 0 := by
  have h1 : abs (2 * t) ≥ 0 := abs_nonneg (2 * t)
  linarith

lemma lem_log2Olog2 :
(fun t : ℝ => Real.log (abs (2 * t) + 4)) =O[Filter.atTop ⊔ Filter.atBot] (fun t : ℝ => Real.log (abs t + 2)) := by

  have h_eq : ∀ t : ℝ, abs (2 * t) + 4 = 2 * (abs t + 2) := by
    intro t
    rw [abs_mul, abs_two]
    ring

  have h_log_decomp : ∀ t : ℝ, Real.log (abs (2 * t) + 4) = Real.log 2 + Real.log (abs t + 2) := by
    intro t
    rw [h_eq]
    have h_pos : 0 < abs t + 2 := by linarith [abs_nonneg t]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h_pos)]

  have h_target_eq : (fun t : ℝ => Real.log (abs (2 * t) + 4)) =
                     (fun t : ℝ => Real.log 2 + Real.log (abs t + 2)) := by
    funext t
    exact h_log_decomp t

  rw [h_target_eq]

  apply Asymptotics.IsBigO.of_bound 2

  filter_upwards with t

  have h_pos_arg : abs t + 2 ≥ 1 := by linarith [abs_nonneg t]
  have h_log_nonneg : 0 ≤ Real.log (abs t + 2) := Real.log_nonneg h_pos_arg
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))

  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith [h_log2_pos.le, h_log_nonneg] : 0 ≤ Real.log 2 + Real.log (abs t + 2))]
  rw [abs_of_nonneg h_log_nonneg]

  have h_bound : Real.log 2 ≤ Real.log (abs t + 2) := by
    apply Real.log_le_log (by norm_num : 0 < (2 : ℝ))
    linarith [abs_nonneg t]

  linarith [h_bound]

lemma lem_Z2bound :
  ∃ C > 1,
     ∀ t : ℝ, 2 < |t| →
      ∀ δ, 0 < δ ∧ δ < 1 →
        (-(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I))).re
          ≤ C * Real.log (abs t + 2) := by
                                                     
  obtain ⟨C₁, hC₁_pos, hbound₁⟩ := lem_explicit2Real2

  have h_log_comp :
      ∀ t : ℝ, 2 < |t| → Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := by
    intro t ht
    have h_pos_2t : 0 < abs (2 * t) + 2 := by linarith [abs_nonneg (2 * t)]
    have h_pos_t : 0 < abs t + 2 := by linarith [abs_nonneg t]
    have h_2t_eq : abs (2 * t) = 2 * abs t := by
      rw [abs_mul, abs_two]

    have h_bound : abs (2 * t) + 2 ≤ 4 * (abs t + 2) := by
      rw [h_2t_eq]
                                         
      linarith [abs_nonneg t]

    have h_4_pos : (0 : ℝ) < 4 := by norm_num
    have h_log_bound : Real.log (abs (2 * t) + 2) ≤ Real.log (4 * (abs t + 2)) :=
      Real.log_le_log h_pos_2t h_bound

    have h_log_mul_eq : Real.log (4 * (abs t + 2)) = Real.log 4 + Real.log (abs t + 2) := by
      exact Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt h_pos_t)

    have h_4_le : (4 : ℝ) ≤ abs t + 2 := by linarith [ht]
    have h_log_4 : Real.log 4 ≤ Real.log (abs t + 2) :=
      Real.log_le_log (by norm_num) h_4_le

    calc Real.log (abs (2 * t) + 2)
      ≤ Real.log (4 * (abs t + 2)) := h_log_bound
      _ = Real.log 4 + Real.log (abs t + 2) := h_log_mul_eq
      _ ≤ Real.log (abs t + 2) + Real.log (abs t + 2) := add_le_add_left h_log_4 _
      _ = 2 * Real.log (abs t + 2) := by ring

  have hC₁_nonneg : 0 ≤ C₁ := le_of_lt (lt_trans zero_lt_one hC₁_pos)

  refine ⟨2 * C₁, ?_, ?_⟩
  ·                   
    linarith [hC₁_pos]
  ·              
    intro t ht δ hδ
    let s := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I

    have h1 : (-(logDerivZeta s)).re ≤ C₁ * Real.log (abs (2 * t) + 2) := hbound₁ t ht δ hδ

    have h3 : Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := h_log_comp t ht

    calc (-(logDerivZeta s)).re
      ≤ C₁ * Real.log (abs (2 * t) + 2) := h1
      _ ≤ C₁ * (2 * Real.log (abs t + 2)) := mul_le_mul_of_nonneg_left h3 hC₁_nonneg
      _ = (2 * C₁) * Real.log (abs t + 2) := by ring

lemma lem_Z1split (delta : ℝ) (_hdelta : delta > 0) (_hdelta_lt1 : delta < 1) (rho : ℂ)
  (_h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) =
    (((analyticOrderAt riemannZeta rho).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re +
    Finset.sum ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
  classical
  set s := Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)
  set f := fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re
  have hmem : rho ∈ s := by
    simpa [s, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using h_rho_in_Zt
                                                            
  have h_decomp : ∑ x ∈ s, f x = f rho + ∑ x ∈ s.erase rho, f x := by
    rw [← Finset.insert_erase hmem]
    rw [Finset.sum_insert (Finset.notMem_erase rho s)]
    simp
  exact h_decomp

lemma re_ofReal_mul_eq (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
  calc
    ((a : ℂ) * z).re = ((a : ℂ).re) * z.re - ((a : ℂ).im) * z.im := by
      simp [Complex.mul_re]
    _ = a * z.re - 0 := by
      simp
    _ = a * z.re := by
      simp

lemma re_ofReal_div_eq (a : ℝ) (z : ℂ) : ((a : ℂ) / z).re = a * (1 / z).re := by
  simp [div_eq_mul_inv]

lemma re_ofReal_div_ge_one (a : ℝ) (z : ℂ) (ha : 1 ≤ a) (hz : 0 ≤ (1 / z).re) : ((a : ℂ) / z).re ≥ (1 / z).re := by
  have hrepr : ((a : ℂ) / z).re = a * (1 / z).re := by
    simp [div_eq_mul_inv, Complex.mul_re]
  have hmul : (1 : ℝ) * (1 / z).re ≤ a * (1 / z).re :=
    mul_le_mul_of_nonneg_right ha hz
  calc
    ((a : ℂ) / z).re = a * (1 / z).re := hrepr
    _ ≥ 1 * (1 / z).re := by exact hmul
    _ = (1 / z).re := by simp [one_mul]

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
                                                                  
  refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
                                                                                          
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

lemma riemannZeta_not_eventually_zero_of_ne_one {s : ℂ} (hs : s ≠ 1) :
  ¬ (∀ᶠ z in nhds s, riemannZeta z = 0) := by
  intro hEvZero
                                                                                            
  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1
                                                    
  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                   
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                 
                                                                 
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta t := by
                                               
          exact differentiableAt_riemannZeta ht
        have hdiff := h1.mul h2
                                                           
        apply hdiff.congr_of_eventuallyEq
        filter_upwards [eventually_ne_nhds ht] with u hu
        simp [H, Function.update_of_ne hu]
      ·                                        
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                     
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := by
        exact differentiableAt_riemannZeta hz
      have hdiff := h1.mul h2
                                                      
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with u hu
      simp [H, Function.update_of_ne hu]
                                                                            
  have hH_analytic : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff
                                             
  have h0_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    intro z _; simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
                                                                                         
  have hEv_ne1 : ∀ᶠ z in nhds s, z ≠ 1 := eventually_ne_nhds hs
  have hEv_H0 : ∀ᶠ z in nhds s, H z = 0 := by
    filter_upwards [hEvZero, hEv_ne1] with z hz_zero hz_ne1
                                        
    have : H z = (z - 1) * riemannZeta z := by simp [H, Function.update_of_ne hz_ne1]
    simp [this, hz_zero]
                                                                              
  have hEqOn : Set.EqOn H (fun _ : ℂ => (0 : ℂ)) Set.univ := by
                           
    have hU : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hH_analytic h0_analytic hU (by simp) hEv_H0
  have hHeq : H = fun _ : ℂ => (0 : ℂ) := by
    funext z; simpa using hEqOn (by simp : z ∈ (Set.univ : Set ℂ))
                                         
  have h2ne1 : (2 : ℂ) ≠ 1 := by norm_num
  have hH2 : H (2 : ℂ) = (2 - 1) * riemannZeta (2 : ℂ) := by
    simp [H]
  have hzeta2_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hprod_zero' : 0 = (2 - 1) * riemannZeta (2 : ℂ) := by
    simpa [hHeq] using hH2
  have hprod_zero : (2 - 1) * riemannZeta (2 : ℂ) = 0 := hprod_zero'.symm
  have hnonzero : (2 - 1) * riemannZeta (2 : ℂ) ≠ 0 := by
    have hcoeff : (2 : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h2ne1
    exact mul_ne_zero hcoeff hzeta2_ne
  exact hnonzero hprod_zero

lemma analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero {f : ℂ → ℂ} {z0 : ℂ}
  (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
  (hnot : ¬ (∀ᶠ z in nhds z0, f z = 0)) :
  1 ≤ (analyticOrderAt f z0).toNat := by
  classical
                                                 
  have hne0 : analyticOrderAt f z0 ≠ 0 := by
    intro h0
    have hzne : f z0 ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hf).1 h0
    exact hzne hzero
                                                                         
  have hneTop : analyticOrderAt f z0 ≠ ⊤ := by
    intro htop
    have hall : (∀ᶠ z in nhds z0, f z = 0) := (analyticOrderAt_eq_top).1 htop
    exact hnot hall
                                          
  rcases WithTop.ne_top_iff_exists.mp hneTop with ⟨n, hn⟩
                             
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hne0
                                            
    simp [hn.symm, hn0]
    rfl
                    
  have hposn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
                                         
  simpa [hn.symm] using! hposn

lemma lem_Z1splitge (delta : ℝ) (hdelta_pos : delta > 0) (hdelta : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) ≥
(1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re := by
  classical
                           
  have hsplit :=
    lem_Z1split delta hdelta_pos hdelta rho h_rho_in_zeroZ h_rho_in_Zt
                                    
  rw [hsplit]
                                       
  have h_rho_ne_one : rho ≠ (1 : ℂ) := by
    intro h
    have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    exact hz1_ne (by simpa [h] using! h_rho_in_zeroZ)
  have hAnal : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta_of_ne_one h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds rho, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  have horder_nat : 1 ≤ (analyticOrderAt riemannZeta rho).toNat :=
    analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero
      hAnal (by simpa using! h_rho_in_zeroZ) hNotEv
  have ha_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho).toNat : ℝ) := by exact_mod_cast horder_nat
  have hz_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re :=
    lem_Re1deltatge0 delta hdelta_pos rho.im rho h_rho_in_Zt
  have hfirst :
      (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re
        ≤ (((((analyticOrderAt riemannZeta rho).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho))).re := by
                               
    simpa [ge_iff_le] using
      (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho).toNat : ℝ)
        ((((1 : ℂ) + delta + rho.im * Complex.I) - rho)) ha_real hz_nonneg)
                                        
  have hsum_nonneg :
      0 ≤ Finset.sum
        ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
        (fun rho1 : ℂ =>
          (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    rcases Finset.mem_erase.mp hmem with ⟨_, hmemS⟩
                                     
    have hZt : rho1 ∈ ZetaZerosNearPoint rho.im := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using hmemS
                    
    have hne1 : rho1 ≠ (1 : ℂ) := by
      intro h
      have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
      have hzero1 : riemannZeta rho1 = 0 := hZt.1
      exact hz1_ne (by simpa [h] using hzero1)
                           
    have hAnal1 : AnalyticAt ℂ riemannZeta rho1 := analyticAt_riemannZeta_of_ne_one hne1
    have hNotEv1 : ¬ (∀ᶠ z in nhds rho1, riemannZeta z = 0) :=
      riemannZeta_not_eventually_zero_of_ne_one hne1
    have hzero1 : riemannZeta rho1 = 0 := hZt.1
    have horder1 : 1 ≤ (analyticOrderAt riemannZeta rho1).toNat :=
      analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero hAnal1 hzero1 hNotEv1
    have ha1_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho1).toNat : ℝ) := by exact_mod_cast horder1
                       
    have hz1_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re :=
      lem_Re1deltatge0 delta hdelta_pos rho.im rho1 hZt
                                           
    have hge :
        (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re ≤
          (((((analyticOrderAt riemannZeta rho1).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1))).re := by
      simpa [ge_iff_le] using
        (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho1).toNat : ℝ)
          ((((1 : ℂ) + delta + rho.im * Complex.I) - rho1)) ha1_real hz1_nonneg)
                                                       
    exact le_trans hz1_nonneg hge
                           
  have h := add_le_add hfirst hsum_nonneg
                             
  simpa using h

lemma lem_1deltatrho0 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
((1 : ℂ) + delta + rho.im * Complex.I - rho) = ((1 : ℝ) + delta - rho.re) := by

  calc (1 : ℂ) + delta + rho.im * Complex.I - rho
    = (1 : ℂ) + delta + rho.im * Complex.I - (rho.re + rho.im * Complex.I) := by rw [Complex.re_add_im]
  _ = (1 : ℂ) + delta - rho.re := by ring
  _ = ((1 : ℝ) + delta - rho.re : ℂ) := by norm_cast

lemma lem_1delsigReal (delta : ℝ) (hdelta_pos : delta > 0) (_hdelta : delta < 1) (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
  rw [lem_1deltatrho0 delta hdelta_pos rho h_rho_in_zeroZ]

  rw [← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_one]

  rw [Complex.div_ofReal_re]
                                                                               
  rw [Complex.ofReal_re]

lemma lem_11delsiginR (delta : ℝ) (hdelta : delta > 0) (_hdelta_lt_1 : delta < 1) (sigma : ℝ) (hsigma : sigma ≤ 1) :
(1 / ((1 : ℂ) + delta - sigma)).im = 0 := by
                                                                
  have h_pos : 1 + delta - sigma > 0 := by
    calc 1 + delta - sigma
      = (1 - sigma) + delta := by ring
      _ ≥ 0 + delta := by linarith [hsigma]
      _ = delta := by simp
      _ > 0 := hdelta

  have h_eq : (1 : ℂ) + delta - sigma = (1 + delta - sigma : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]

  rw [h_eq]

  rw [Complex.div_ofReal_im]

  rw [Complex.one_im]

  simp

lemma lem_11delsiginR2 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta - rho.re)).im = 0 := by
                                                  
  have h_zeta_zero : riemannZeta rho = 0 := h_rho_in_zeroZ

  have h_rho_form : rho = rho.re + rho.im * Complex.I := by simp [Complex.re_add_im]

  rw [h_rho_form] at h_zeta_zero

  have h_rho_re_le_1 : rho.re ≤ 1 := lem_sigmale1 rho.re rho.im h_zeta_zero

  exact lem_11delsiginR delta hdelta hdelta_lt_1 rho.re h_rho_re_le_1

lemma lem_ReReal (x : ℝ) : (x : ℂ).re = x := Complex.ofReal_re x

lemma lem_1delsigReal2 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta - rho.re)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                                           
  have h_eq : (1 : ℂ) + delta - rho.re = (1 + delta - rho.re : ℝ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]

  rw [h_eq]

  rw [Complex.div_ofReal_re]

  rw [Complex.one_re]

lemma lem_re_inv_one_plus_delta_minus_rho_real (delta : ℝ) (hdelta : delta > 0)  (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
                                                      
  rw [lem_1deltatrho0 delta hdelta rho h_rho_in_zeroZ]
                               
  exact lem_1delsigReal2 delta hdelta rho h_rho_in_zeroZ

lemma lem_Z1splitge2 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + rho.im * Complex.I - rho1)).re) ≥
1 / ((1 : ℝ) + delta - rho.re) := by
                                                    
  have h1 := lem_Z1splitge delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt
                                                                                  
  have h2 := lem_re_inv_one_plus_delta_minus_rho_real delta hdelta rho h_rho_in_zeroZ
                        
  rw [← h2]
  exact h1

lemma lem_Z1splitge3 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (sigma t : ℝ) (rho : ℂ)
  (h_rho_eq : rho = sigma + t * Complex.I) (h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint t) :
(Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + t * Complex.I) - rho1)) ).re ≥ 1 / ((1 : ℝ) + delta - sigma) := by
                                                                                   
  rw [lem_sumrho1 t delta hdelta hdelta_lt_1]

  have h_rho_im : rho.im = t := by
    rw [h_rho_eq]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im]
  have h_rho_re : rho.re = sigma := by
    rw [h_rho_eq]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re]

  have h_rho_in_Zt' : rho ∈ ZetaZerosNearPoint rho.im := by
    rw [h_rho_im]
    exact h_rho_in_Zt

  have h_bound := lem_Z1splitge2 delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt'

  convert h_bound using 1
                                                       
  simp_rw [← h_rho_im]
                                                             
  rw [h_rho_re]

lemma lem_rho_in_Zt (delta : ℝ) (hdelta : delta > 0) (t : ℝ)
  (h_rho_zero : (1 : ℂ) + delta + t * Complex.I ∈ zeroZ) :
  (1 : ℂ) + delta + t * Complex.I ∈ ZetaZerosNearPoint t := by

  let ρ : ℂ := (1 : ℂ) + delta + t * Complex.I

  have h_re : ρ.re > 1 := by
    simp [ρ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re]
    linarith [hdelta]

  have h_nonzero : riemannZeta ρ ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    exact le_of_lt h_re

  have h_zero : riemannZeta ρ = 0 := h_rho_zero

  exact absurd h_zero h_nonzero

lemma Z1bound :
  ∃ C > 1,
    ∀ (delta : ℝ), (0 < delta ∧ delta < 1) →
      ∀ t : ℝ, 2 < |t| →
        ∀ s : ℂ, s ∈ zeroZ ∧ s.im = t →
          (-(logDerivZeta ((1 : ℂ) + delta + t * Complex.I))).re
            ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
  classical
                                            
  obtain ⟨C0, hC0gt1, hExp⟩ := lem_explicit1RealReal
                                                                                  
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  let C : ℝ := max (C0 + 3 / Real.log 4) 2
  have hCgt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hCgt1, ?_⟩
  intro delta hdelta t ht s hs
                  
  set sp : ℂ := (1 : ℂ) + delta + t * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (sp - rho1)).re)
                                                                        
  have h_bound : abs ((logDerivZeta sp).re - Sre)
        ≤ C0 * Real.log (abs t + 2) := by
    simpa [sp, S, Sre] using hExp t ht delta hdelta
                                                                         
  have h_left : -(C0 * Real.log (abs t + 2)) ≤ (logDerivZeta sp).re - Sre :=
    (abs_le.mp h_bound).1
  have h_neg : -((logDerivZeta sp).re - Sre) ≤ C0 * Real.log (abs t + 2) := by
    simpa using neg_le_neg h_left
  have h_isol : - (logDerivZeta sp).re ≤ C0 * Real.log (abs t + 2) - Sre := by
    have := sub_le_sub_right h_neg Sre
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                              
  have hS_nonneg : 0 ≤ Sre := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    have hZt : rho1 ∈ ZetaZerosNearPoint t := by
      simpa [S, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite t)] using hmem
                                   
    simpa [sp] using
      (lem_Re1deltatge0m delta hdelta.1 t hdelta.2 rho1 hZt)
                                 
  have h_basic : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := by
    have h_drop : C0 * Real.log (abs t + 2) - Sre ≤ C0 * Real.log (abs t + 2) :=
      sub_le_self _ hS_nonneg
    exact le_trans h_isol h_drop
                                              
  by_cases hmem : s ∈ ZetaZerosNearPoint t
  ·                                                               
    set sigma : ℝ := s.re
    have h_rho_eq : s = (sigma : ℂ) + t * Complex.I := by
      have : s = s.re + s.im * Complex.I := by simp [Complex.re_add_im]
      simpa [sigma, hs.2] using this
                                              
    have hsum_rew := lem_sumrho1 t delta hdelta.1 hdelta.2
    have h_sum_ge' :=
      lem_Z1splitge3 delta hdelta.1 hdelta.2 sigma t s h_rho_eq hs.1 hmem
    have h_sum_ge : Sre ≥ 1 / ((1 : ℝ) + delta - sigma) := by
      simpa [sp, S, Sre, hsum_rew] using h_sum_ge'
                                                                                  
    have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      have : (1 / ((1 : ℝ) + delta - sigma)) ≤ Sre := h_sum_ge
      have := sub_le_sub_left this (C0 * Real.log (abs t + 2))
      exact le_trans h_isol (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
                                              
    have hCge : C0 ≤ C :=
      le_trans (by
        have : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
        have := add_le_add_right this C0
        simpa using this) (le_max_left _ _)
                                   
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have h_enlarge : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) :=
      mul_le_mul_of_nonneg_right hCge hY_nonneg
    have h2 : C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) ≤
              C * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (sub_le_sub_right h_enlarge (1 / ((1 : ℝ) + delta - sigma)))
    have := le_trans h1 h2
    simpa [sp, sigma, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  ·                                                                                           
                                                                             
    have h_notle : ¬ ‖s - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) := by
      intro hle
      exact hmem ⟨hs.1, hle⟩
    have hdist_gt : (5/6 : ℝ) < ‖s - ((3/2 : ℂ) + t * Complex.I)‖ := not_le.mp h_notle
                                                                                            
    have h_re : (s - ((3/2 : ℂ) + t * Complex.I)).re = s.re - (3/2 : ℝ) := by
      simp [Complex.sub_re, Complex.add_re]
    have h_im : (s - ((3/2 : ℂ) + t * Complex.I)).im = 0 := by
      have : (s - ((3/2 : ℂ) + t * Complex.I)).im = s.im - t := by
        simp [Complex.sub_im, Complex.add_im]
      simp [hs.2]
    have h_eq : s - ((3/2 : ℂ) + t * Complex.I) = (((s.re - (3/2 : ℝ)) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [h_re]
      · simp [h_im]
    have hdist_real : ‖s - ((3/2 : ℂ) + t * Complex.I)‖ = |s.re - (3/2 : ℝ)| := by
      simpa [h_eq] using complex_abs_of_real (s.re - (3/2 : ℝ))
    have habs_gt : (5/6 : ℝ) < |s.re - (3/2 : ℝ)| := by simpa [hdist_real] using hdist_gt
                                 
    have h0 : riemannZeta (s.re + s.im * Complex.I) = 0 := by
      simpa [Complex.re_add_im] using! hs.1
    have hs_le1 : s.re ≤ 1 := lem_sigmale1 s.re s.im h0
                                                        
    have h_nonpos : s.re - (3/2 : ℝ) ≤ 0 := by linarith [hs_le1]
    have h_abs_eq : |s.re - (3/2 : ℝ)| = (3/2 : ℝ) - s.re := by
      have : |s.re - (3/2 : ℝ)| = -(s.re - (3/2 : ℝ)) := abs_of_nonpos h_nonpos
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h_gt' : (5/6 : ℝ) < (3/2 : ℝ) - s.re := by simpa [h_abs_eq] using habs_gt
    have hs_le_23 : s.re ≤ (2/3 : ℝ) := by linarith [h_gt']
                                                                    
    have hden_ge : (1/3 : ℝ) ≤ 1 + delta - s.re := by
      have : (1/3 : ℝ) ≤ 1 - s.re := by linarith [hs_le_23]
      have : 1 - s.re ≤ 1 + delta - s.re := by linarith [hdelta.1]
      exact le_trans ‹(1/3 : ℝ) ≤ 1 - s.re› this
    have hone_div_le3 : 1 / (1 + delta - s.re) ≤ (3 : ℝ) := by
      have : 1 / (1 + delta - s.re) ≤ 1 / (1/3 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/3) hden_ge
      simpa [one_div] using this
    have hneg_ge : - (3 : ℝ) ≤ - (1 / (1 + delta - s.re)) := by
      simpa using (neg_le_neg hone_div_le3)
                                            
    have hlog_ge : Real.log 4 ≤ Real.log (abs t + 2) := by
      have : (4 : ℝ) < abs t + 2 := by linarith [ht]
      exact Real.log_le_log (by norm_num) (le_of_lt this)
    have hC_ge_add : C ≥ C0 + 3 / Real.log 4 := by exact le_max_left _ _
    have hCminus : C - C0 ≥ 3 / Real.log 4 := by linarith
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have hmul1 : (3 / Real.log 4) * Real.log 4 ≤ (3 / Real.log 4) * Real.log (abs t + 2) := by
      have hk_nonneg : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
      exact mul_le_mul_of_nonneg_left hlog_ge hk_nonneg
    have hmul2 : (3 / Real.log 4) * Real.log (abs t + 2) ≤ (C - C0) * Real.log (abs t + 2) := by
      exact mul_le_mul_of_nonneg_right hCminus hY_nonneg
    have hmul_ge3 : (3 : ℝ) ≤ (C - C0) * Real.log (abs t + 2) := by
      have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
      have hcalc : (3 / Real.log 4) * Real.log 4 = 3 := by
        simp [div_eq_mul_inv, hne5]
      have : (3 / Real.log 4) * Real.log 4 ≤ (C - C0) * Real.log (abs t + 2) :=
        le_trans hmul1 hmul2
      simpa [hcalc] using this
                                 
    have hCmul' : C0 * Real.log (abs t + 2) + 3 ≤ C * Real.log (abs t + 2) := by
      have : C0 * Real.log (abs t + 2) + 3 ≤ C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        exact add_le_add_right hmul_ge3 _
      have hcalc : C * Real.log (abs t + 2) =
          C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        ring
      simpa [hcalc, add_comm, add_left_comm, add_assoc] using this
                                                                              
    have : (-(logDerivZeta sp)).re ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
      have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := h_basic
      have h2 : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) - 3 := by
        linarith [hCmul']
      have h3 : C * Real.log (abs t + 2) - 3 ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
        have := add_le_add_left hneg_ge (C * Real.log (abs t + 2))
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      exact le_trans h1 (le_trans h2 h3)
    simpa [sp, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

lemma Z0boundRe :
Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => (- (logDerivZeta ((1 : ℂ) + delta))).re - (1 / delta)) (fun _ => (1 : ℝ)) := by
                                              
  have h := Z0bound

  have h_eq : (fun (delta : ℝ) => (- (logDerivZeta ((1 : ℂ) + delta))).re - (1 / delta)) =
              (fun (delta : ℝ) => (-logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))).re) := by
    ext delta
    rw [Complex.sub_re, Complex.neg_re]
                                                 
    have : (1 / (delta : ℂ)).re = 1 / delta := by
      rw [Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
      simp [Complex.normSq_ofReal]
    rw [this]

  rw [h_eq]

  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc] with delta h_delta
  have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
  rw [this] at h_delta
  have : ‖(1 : ℝ)‖ = (1 : ℝ) := by simp
  rw [this]
  exact le_trans (Complex.abs_re_le_norm _) h_delta

lemma extract_bigO_bound_Z0 (delta : ℝ) (_hdelta : delta > 0) : ∃ C0 > 0, (-logDerivZeta ((1 : ℂ) + delta)).re ≤ 1 / delta + C0 := by

  let target := (-logDerivZeta ((1 : ℂ) + delta)).re
  let base := 1 / delta

  use max 1 (target - base + 1)

  constructor
  ·               
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (target - base + 1))

  ·                                            

    by_cases h : target - base + 1 ≤ 1
    ·                                           
      have h_max : max 1 (target - base + 1) = 1 := max_eq_left h
      rw [h_max]

      linarith [h]
    ·                                                           
      have h_max : max 1 (target - base + 1) = target - base + 1 := max_eq_right (le_of_not_ge h)
      rw [h_max]
                                                              
      linarith

lemma uniform_bound_Z0 : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → (- (logDerivZeta ((1 : ℂ) + δ))).re ≤ 1 / δ + C0 := by
                                                             
  let f : ℝ → ℝ := fun δ => (- (logDerivZeta ((1 : ℂ) + δ))).re - (1 / δ)
                                           
  have hO := Z0boundRe
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
                                                                                       
  have h1norm : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                       
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℝ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    simpa using (by simpa using hδ)
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h1norm with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  have hnorm_le_C0 : ‖f δ‖ ≤ max c 0 := le_trans hnorm_le_c (le_max_left _ _)
                                    
  have h_upper : f δ ≤ max c 0 := by
    have : |f δ| ≤ max c 0 := by simpa [Real.norm_eq_abs] using hnorm_le_C0
    exact (abs_le.mp this).2
                                        
  have := (sub_le_iff_le_add).1 h_upper
  simpa [f, add_comm] using this

lemma eventually_atTop_sup_atBot_iff_abs {P : ℝ → Prop} :
  (∀ᶠ t in (Filter.atTop ⊔ Filter.atBot), P t) ↔ ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| → P t := by
  constructor
  · intro h
    have h' := (Filter.eventually_sup).1 h
    rcases h' with ⟨hTop, hBot⟩
    rcases (Filter.eventually_atTop).1 hTop with ⟨A, hA⟩
    rcases (Filter.eventually_atBot).1 hBot with ⟨B, hB⟩
    refine ⟨max A (-B), ?_⟩
    intro t ht
    have hcases : max A (-B) ≤ t ∨ max A (-B) ≤ -t := (le_abs).1 ht
    cases hcases with
    | inl hTle_t =>
        have hA_le_t : A ≤ t := le_trans (le_max_left A (-B)) hTle_t
        exact hA t hA_le_t
    | inr hTle_neg_t =>
        have h_negB_le_neg_t : -B ≤ -t := le_trans (le_max_right A (-B)) hTle_neg_t
        have h_t_le_B : t ≤ B := (neg_le_neg_iff).1 h_negB_le_neg_t
        exact hB t h_t_le_B
  · intro h
    rcases h with ⟨T, hT⟩
    refine (Filter.eventually_sup).2 ?_
    constructor
    ·         
      refine (Filter.eventually_atTop).2 ?_
      refine ⟨max T 0, ?_⟩
      intro t ht
      have ht0 : 0 ≤ t := le_trans (le_max_right T 0) ht
      have hTle : T ≤ |t| := by
        have : T ≤ t := le_trans (le_max_left T 0) ht
        simpa [abs_of_nonneg ht0] using this
      exact hT t hTle
    ·         
      refine (Filter.eventually_atBot).2 ?_
      refine ⟨-max T 0, ?_⟩
      intro t ht
      have ht0 : t ≤ 0 := by
        have hnegmax_le_0 : -max T 0 ≤ 0 := by
          simp
        exact le_trans ht hnegmax_le_0
      have hTle : T ≤ |t| := by
        have h1 : max T 0 ≤ -t := by
          have := (neg_le_neg ht)
                                  
          simpa using this
        have : T ≤ -t := le_trans (le_max_left T 0) h1
        simpa [abs_of_nonpos ht0] using this
      exact hT t hTle

lemma re_sum_three (a b : ℝ) (x y z : ℂ) : ((a * x) + (b * y) + z).re = a * x.re + b * y.re + z.re := by
                                                                    
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, add_assoc]

lemma log_abs_add_two_ge_one (t : ℝ) (ht : Real.exp 1 - 2 ≤ |t|) : (1 : ℝ) ≤ Real.log (|t| + 2) := by
  have hx : Real.exp 1 ≤ |t| + 2 := by
    have h' := add_le_add_left ht (2 : ℝ)
    simpa [sub_add_cancel] using! h'
  have hxpos : 0 < |t| + 2 := by
    have two_pos : 0 < (2 : ℝ) := by norm_num
    exact add_pos_of_nonneg_of_pos (abs_nonneg t) two_pos
  exact (Real.le_log_iff_exp_le hxpos).2 hx

lemma log_abs_add_two_ge_of_threshold (K t : ℝ) (ht : Real.exp K - 2 ≤ |t|) : K ≤ Real.log (|t| + 2) := by
  have hx : Real.exp K ≤ |t| + 2 := by
    have h' := add_le_add_left ht (2 : ℝ)
    simpa [sub_add_cancel] using! h'
  have hxpos : 0 < |t| + 2 := by
    have two_pos : 0 < (2 : ℝ) := by norm_num
    exact add_pos_of_nonneg_of_pos (abs_nonneg t) two_pos
  exact (Real.le_log_iff_exp_le hxpos).2 hx

lemma re_ofReal_add_ofReal_add (a b : ℝ) (z : ℂ) : (a + b + z).re = a + b + z.re := by
  simp [Complex.add_re, Complex.ofReal_re, add_assoc]

lemma algebraic_rewrite_RHS (δ s L C0 C1 C2 : ℝ) :
  3 * (1 / δ + C0) + 4 * (-(1 / (1 + δ - s)) + C1 * L) + C2 * L =
    3 / δ - 4 / (1 + δ - s) + (4 * C1 + C2) * L + 3 * C0 := by
  have hA : 3 * (1 / δ + C0) = 3 * (1 / δ) + 3 * C0 := by
    simp [mul_add]
  have hB2 :
      4 * (-(1 / (1 + δ - s)) + C1 * L) =
        -(4 * (1 / (1 + δ - s))) + (4 * C1) * L := by
    calc
      4 * (-(1 / (1 + δ - s)) + C1 * L)
          = 4 * (-(1 / (1 + δ - s))) + 4 * (C1 * L) := by
            simp [mul_add]
      _ = -(4 * (1 / (1 + δ - s))) + (4 * C1) * L := by
        simp [mul_comm, mul_assoc]
  calc
    3 * (1 / δ + C0) + 4 * (-(1 / (1 + δ - s)) + C1 * L) + C2 * L
        = (3 * (1 / δ) + 3 * C0) + 4 * (-(1 / (1 + δ - s)) + C1 * L) + C2 * L := by
          rw [hA]
    _ = (3 * (1 / δ) + 3 * C0) + (-(4 * (1 / (1 + δ - s))) + (4 * C1) * L) + C2 * L := by
      rw [hB2]
    _ = (3 / δ + 3 * C0) + (- 4 / (1 + δ - s) + (4 * C1) * L) + C2 * L := by
      simp [div_eq_mul_inv]
    _ = 3 / δ - 4 / (1 + δ - s) + (4 * C1) * L + C2 * L + 3 * C0 := by
      ring
    _ = 3 / δ - 4 / (1 + δ - s) + (4 * C1 + C2) * L + 3 * C0 := by
      ring

lemma absorb_pos_constant_into_log {L A c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) : A * L + c ≤ (A + c) * L := by
                                             
  have hc_le : c ≤ L * c := by
    have h := mul_le_mul_of_nonneg_right hL hc
    simpa [one_mul] using h
                                        
  have h0 : A * L + c ≤ A * L + L * c := by
    exact add_le_add_right hc_le (A * L)
  calc
    A * L + c ≤ A * L + L * c := h0
    _ = A * L + c * L := by simp [mul_comm]
    _ = (A + c) * L := by simp [right_distrib]

lemma neg_logDeriv_zeta_eq_vonMangoldt_sum (s : ℂ) (hs : 1 < s.re) : -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
                                                                                     
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

  have h2 : -deriv riemannZeta s / riemannZeta s = LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s := h1.symm
                                                                                                                 
  have h3 : -(deriv riemannZeta s / riemannZeta s) = -deriv riemannZeta s / riemannZeta s := by ring
  rw [h3, h2]

  rw [LSeries]
  congr 1
  ext n
  rw [LSeries.term_def]
  split_ifs with h_zero
  ·                                
    simp [h_zero]
  ·                                                                     
    rw [div_eq_mul_inv, Complex.cpow_neg]

lemma zeta1zetaseries {s : ℂ} (hs : 1 < s.re) :
-logDerivZeta s = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold logDerivZeta
                                                                                                                       
  exact neg_logDeriv_zeta_eq_vonMangoldt_sum s hs

lemma zeta1zetaseriesxy (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I)) := by
  apply zeta1zetaseries

  have h : (x + y * I).re = x := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma Zconverges1 (x y : ℝ) (hx : 1 < x) : riemannZeta (x + y * I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re

  have h : (x + y * I).re = x := by
    rw [Complex.add_re, Complex.ofReal_re]
    simp [Complex.mul_re]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma complex_re_of_real_add_imag (x y : ℝ) : (x + y * I).re = x := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
                                                                           
  right
  exact Complex.I_re

lemma vonMangoldt_LSeriesSummable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
                                                                            
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs

lemma summable_of_support_singleton {α : Type*} [SeminormedAddCommGroup α] (f : ℕ → α) (n₀ : ℕ) (h : ∀ n : ℕ, n ≠ n₀ → f n = 0) : Summable f := by
                                                     
  have h_finite_support : Set.Finite (Function.support f) := by
                                       
    have h_subset : Function.support f ⊆ {n₀} := by
      intro n hn

      by_contra h_ne
                                                 
      have h_zero : f n = 0 := h n h_ne
                                     
      simp [Function.mem_support] at hn
      exact hn h_zero
                                                                 
    exact Set.Finite.subset (Set.finite_singleton n₀) h_subset

  exact summable_of_hasFiniteSupport h_finite_support

lemma summable_of_summable_add_sub {α : Type*} [SeminormedAddCommGroup α] (f g h : ℕ → α) (h_eq : f = g + h) (hf : Summable f) (hh : Summable h) : Summable g := by

  have g_eq_f_sub_h : g = f - h := by
                                           
    rw [← sub_eq_iff_eq_add] at h_eq
    exact h_eq.symm

  rw [g_eq_f_sub_h]

  exact hf.sub hh

lemma LSeriesSummable_to_summable (f : ℕ → ℂ) (s : ℂ) (h : LSeriesSummable f s) : Summable (fun n => f n * (n : ℂ) ^ (-s)) := by
                                                          
  have h_term_summable : Summable (LSeries.term f s) := h

  have h_eq_nonzero : ∀ n : ℕ, n ≠ 0 → LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, Complex.cpow_neg]

  let diff := fun n => LSeries.term f s n - f n * (n : ℂ) ^ (-s)

  have h_diff_support : ∀ n : ℕ, n ≠ 0 → diff n = 0 := by
    intro n hn
    simp only [diff]
    rw [h_eq_nonzero n hn]
    simp

  have h_diff_summable : Summable diff := by
                                              
    apply summable_of_support_singleton diff 0 h_diff_support

  have h_rw : LSeries.term f s = (fun n => f n * (n : ℂ) ^ (-s)) + diff := by
    ext n
    simp only [diff, Pi.add_apply]
    ring

  exact summable_of_summable_add_sub (LSeries.term f s) (fun n => f n * (n : ℂ) ^ (-s)) diff h_rw h_term_summable h_diff_summable

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) := by
                                                                                                
  have h_nonzero : riemannZeta (x + y * I) ≠ 0 := Zconverges1 x y hx

  have h_re_gt_one : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  have h_L_summable : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) :=
    vonMangoldt_LSeriesSummable (x + y * I) h_re_gt_one

  have h_summable : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    LSeriesSummable_to_summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) h_L_summable

  have h_hasSum : HasSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    h_summable.hasSum

  have h_hasSum_re : HasSum (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re :=
    Complex.hasSum_re h_hasSum

  exact h_hasSum_re.summable

lemma exprule (n : ℕ) (hn : n ≥ 1) (alpha beta : ℂ) : (n : ℂ) ^ (alpha + beta) = (n : ℂ) ^ alpha * (n : ℂ) ^ beta := by
  apply Complex.cpow_add
                              
  rw [Nat.cast_ne_zero]
                        
  rw [← Nat.one_le_iff_ne_zero]
  exact hn

lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    Complex.cpow (n : ℂ) (-(x + y * I)) = Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
                                              
  have h : -(x + y * I) = (-x : ℂ) + (-(y * I)) := by ring
  rw [h]
                                                         
  exact lem_exprule n hn (-x : ℂ) (-(y * I))

lemma lem_zeta1zetaseriesxy2 (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (Complex.cpow (n : ℂ) ((-x) : ℂ)) * (Complex.cpow (n : ℂ) (-(y * I))) := by
                            
  rw [zeta1zetaseriesxy x y hx]
                                             
  congr 1
  ext n
                      
  rw [← Complex.cpow_eq_pow]
                                                          
  by_cases h : n = 0
  ·                                
    simp [h]
  ·                                 
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_nxy n hn x y]
                                                          
    ring

lemma complex_add_re_ofReal_mul_I (x y : ℝ) : (x + y * I).re = x := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
                                  
  have h : I.re = 0 := Complex.I_re
  rw [h]
  simp

lemma LSeriesSummable_to_explicit_summable (x y : ℝ) (_hx : 1 < x) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) → Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
  intro h_summable

  have h_vm_zero : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
    simp

  have h_eq : ∀ n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n =
    (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
    intro n
                                                     
    rw [LSeries.term_def₀ h_vm_zero]

    rw [← Complex.cpow_eq_pow]

    by_cases hn : n = 0
    ·                                
      simp [hn]
    ·                                    
      have hn_ge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [lem_nxy n hn_ge x y]
      ring

  have h_term_summable : Summable (fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n) := by
    exact h_summable

  convert h_term_summable using 1
  ext n
  exact (h_eq n).symm

lemma Zseriesconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
                                                        
  have h_zeta_ne_zero := Zconverges1 x y hx

  have h_series := lem_zeta1zetaseriesxy2 x y hx

  have h_re : 1 < (x + y * I).re := by
    rw [complex_add_re_ofReal_mul_I]
    exact hx

  have h_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re

  exact LSeriesSummable_to_explicit_summable x y hx h_summable

lemma lem_realnx (n : ℕ) (x : ℝ) (_hn : n ≥ 1) (_hx : x ≥ 1) :
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x) ≥ 0 := by
  apply mul_nonneg
  ·                                             
    exact ArithmeticFunction.vonMangoldt_nonneg
  ·                           
    apply Real.rpow_nonneg
                       
    exact Nat.cast_nonneg n

lemma sumReal {v : ℕ → ℂ} {v_sum : ℂ} (h_sum : HasSum v v_sum) :
    HasSum (fun n => (v n).re) v_sum.re := by
  exact Complex.hasSum_re h_sum

lemma sumRealLambda (x y : ℝ) (hx : 1 < x) :
    (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
    ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
  apply Complex.re_tsum
  exact Zseriesconverges1 x y hx

lemma lem_sumRealZ (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                         
  rw [lem_zeta1zetaseriesxy2 x y hx]
                                                   
  exact sumRealLambda x y hx

lemma complex_cpow_neg_real (n : ℕ) (x : ℝ) (_hn : n ≥ 1) : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
                                     
  have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
                                   
  rw [Complex.cpow_eq_pow]
                                                   
  rw [Complex.ofReal_cpow h_nonneg (-x)]
                                          
  congr 1
                                 
  simp

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                              
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ) := by
                                                
    have h_real_pow : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      exact complex_cpow_neg_real n x hn

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ)) * Complex.cpow (n : ℂ) (-(y * I)) := by
    rw [mul_assoc]

  rw [h2, h1]

  exact lem_realbw b (Complex.cpow (n : ℂ) (-(y * I)))

lemma ReZseriesRen (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
  rw [lem_sumRealZ x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact RealLambdaxy n x y hn hx

lemma Rezeta1zetaseries (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  rw [ReZseriesRen x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [← lem_eacosalog3 n hn y]
                                                                                          
    congr 1
                                                                        
    rw [Complex.cpow_eq_pow]
                                     
    simp [I]

lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
                                                   
  rw [lem_nxy n hn x y]

  rw [← mul_assoc]

  rw [RealLambdaxy n x y hn hx]

  have h_cpow : (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-(y * I))).re := by
    rw [Complex.cpow_eq_pow]

  have h_I : -(y * I) = -y * Complex.I := by
    simp [I]

  rw [h_cpow, h_I]

  rw [lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
                                                                           
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) :=
    ReZconverges1 x y hx

  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]

lemma Rezetaseries2t (x t : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (2 * t * Real.log (n : ℝ))) := by
                                                  
  exact Rezetaseries_convergence x (2 * t) hx

lemma lem_cost0 (n : ℕ) (_hn : n ≥ 1) (t : ℝ) (ht : t = 0) : Real.cos (t * Real.log (n : ℝ)) = 1 := by
  rw [ht]
  simp

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
                                              
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
                                             
  convert h1 using 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_cost0 n hn 0 rfl]
    ring

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
                                             
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
                                           
  have hO := Z0bound
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                             
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  exact le_trans hnorm_le_c (le_max_left _ _)

lemma cpow_neg_zero_I (z : ℂ) : z ^ (-(0 : ℝ) * Complex.I) = (1 : ℂ) := by
  simp

lemma tsum_nonneg_of_nonneg {f : ℕ → ℝ} (hnon : ∀ n, 0 ≤ f n) : 0 ≤ ∑' n, f n := by
  simpa using (tsum_nonneg hnon)

lemma vonMangoldt_rpow_nonneg (x : ℝ) : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) := by
  intro n
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (n : ℝ) ^ (-x) := by
    exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) _
  simpa using mul_nonneg h1 h2

lemma cpow_neg_real_of_nat (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
  (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
  simpa using complex_cpow_neg_real n x hn

lemma norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt (x : ℝ) (hx : 1 < x) :
  ‖-logDerivZeta (x : ℂ)‖ = |∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x))| := by
                                                    
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hseries := zeta1zetaseries (s := (x : ℂ)) hx'
                                                                                      
  let g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
  have hterm : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)) = (g n : ℂ) := by
    intro n
    by_cases h : n = 0
    ·                                               
      have hv0C : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
        simp
      have hv0R : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        simp
      simp [g, h, hv0R]
    ·                                               
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hcp : (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) :=
        complex_cpow_neg_real n x hn
                                              
      have : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ))
              = Complex.ofReal (ArithmeticFunction.vonMangoldt n) * Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simp [hcp]
      simpa [g, Complex.ofReal_mul] using this
                                                          
  have hsum_eq : (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = ∑' n, (g n : ℂ) := by
                                             
    have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = (fun n => (g n : ℂ)) := funext hterm
    simp [hfun]
                                                                     
  have hsum_ofReal : (∑' n, (g n : ℂ)) = Complex.ofReal (∑' n, g n) := by
    simpa using (Complex.ofReal_tsum g).symm
                                                                                               
  have hval : -logDerivZeta (x : ℂ) = Complex.ofReal (∑' n, g n) := by
                                         
    simpa [hsum_eq, hsum_ofReal] using hseries
                                                                            
  calc
    ‖-logDerivZeta (x : ℂ)‖ = ‖Complex.ofReal (∑' n, g n)‖ := by simp [hval]
    _ = |∑' n, g n| := by
      exact (RCLike.norm_ofReal (K := ℂ) (∑' n, g n))

lemma tsum_le_of_nonneg_of_le {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (_hnonneg : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n) : (∑' n, f n) ≤ (∑' n, g n) := by
  classical
  exact Summable.tsum_le_tsum hle hf hg

lemma rpow_neg_antitone {a x y : ℝ} (ha : 1 ≤ a) (hxy : x ≥ y) : a ^ (-x) ≤ a ^ (-y) := by

  simpa using (Real.rpow_le_rpow_of_exponent_le ha (neg_le_neg hxy))

lemma isPrimePow_zero_false : IsPrimePow 0 = False := by
  apply propext
  constructor
  · intro h
    rcases (isPrimePow_nat_iff 0).1 h with ⟨p, k, hp, hkpos, hk⟩
    have hpnz : (p : ℕ) ≠ 0 := by
      exact ne_of_gt (Nat.Prime.pos hp)
    have hpow_ne : (p : ℕ) ^ k ≠ 0 := pow_ne_zero _ hpnz
    exact (hpow_ne (by simp [hk]))
  · intro hFalse
    exact hFalse.elim

lemma bounded_on_compact_interval (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) : ∃ Cmid ≥ 0, ∀ δ : ℝ, a ≤ δ → δ ≤ b → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid := by
                                      
  let s : Set ℝ := Set.Icc a b
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))

  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                                 
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                           
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                     
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) z := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hz] with u hu using by
        simp [H, Function.update_of_ne hu]

  let G : ℂ → ℂ := fun z => - (deriv H z) / H z

  have h_eq_on_pos : ∀ ⦃δ : ℝ⦄, 0 < δ →
      (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) = G ((1 : ℂ) + δ) := by
    intro δ hδ
                    
    let z : ℂ := (1 : ℂ) + δ
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ : ℝ) = 1 := by
        simpa [z, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ = 0 := by linarith
      exact (ne_of_gt hδ) this
    have hzeta_ne : riemannZeta z ≠ 0 := by
      have : 1 < z.re := by simpa [z, Complex.add_re, Complex.ofReal_re] using by linarith
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt this)

    have h_id_deriv : deriv (fun u : ℂ => u - 1) z = 1 := by
      exact ((hasDerivAt_id z).sub_const 1).deriv
    have h_log_id : logDeriv (fun u : ℂ => u - 1) z = 1 / (z - 1) := by
      simp [logDeriv_apply, h_id_deriv]
    have hz1 : z - 1 ≠ 0 := by simpa using sub_ne_zero.mpr hz_ne_one
    have hζ : riemannZeta z ≠ 0 := hzeta_ne

    have h_deriv_mul : deriv (fun u : ℂ => (u - 1) * riemannZeta u) z
          = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2).deriv

    have h_prodLog :
        logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z =
          logDeriv (fun u : ℂ => u - 1) z + logDerivZeta z := by
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz_ne_one)
      have hfnz : (fun u : ℂ => u - 1) z ≠ 0 := by simpa using hz1
      have hgnz : riemannZeta z ≠ 0 := hζ
      simpa [logDerivZeta] using!
        (logDeriv_mul (x := z) (f := fun u : ℂ => u - 1) (g := riemannZeta) hfnz hgnz h1 h2)

    have h_step : -logDerivZeta z - (1 / (z - 1))
        = - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z := by
      have : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
            = 1 / (z - 1) + logDerivZeta z := by
        simpa [h_log_id, add_comm] using h_prodLog
      have hneg : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
                 = - (1 / (z - 1) + logDerivZeta z) := by
        simpa using congrArg Neg.neg this
      simpa [sub_eq_add_neg, add_comm] using hneg.symm

    have h_H_eq : H z = (z - 1) * riemannZeta z := by
      simp [H, Function.update_of_ne hz_ne_one]

    have h_eq_event : (fun u : ℂ => H u) =ᶠ[nhds z] (fun u : ℂ => (u - 1) * riemannZeta u) := by
      filter_upwards [eventually_ne_nhds hz_ne_one] with u hu
      simp [H, Function.update_of_ne hu]

    have h_hasDeriv_prod :
        HasDerivAt (fun u : ℂ => (u - 1) * riemannZeta u)
          (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2)

    have h_hasDeriv_H :
        HasDerivAt H (riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
      h_hasDeriv_prod.congr_of_eventuallyEq h_eq_event

    have h_dH : deriv H z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      simpa using h_hasDeriv_H.deriv

    have h_log_to_G : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = G z := by
      have h' : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = (deriv H z) / H z := by
        simp [logDeriv_apply, h_H_eq, h_dH, h_deriv_mul]
      have hneg' := congrArg (fun w => -w) h'
      simpa [G, neg_div] using hneg'

    have : -logDerivZeta z - (1 / (z - 1)) = G z := by
      simpa using h_step.trans h_log_to_G

    simpa [z] using this

  let F : ℝ → ℂ := fun δ => G ((1 : ℂ) + δ)

  have hH_analytic_univ : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff

  have hF_contOn : ContinuousOn F s := by
    intro δ0 hδ0
                           
    let s0 : ℂ := (1 : ℂ) + δ0
    have hδ0pos : 0 < δ0 := lt_of_lt_of_le h0 hδ0.1
    have hs0_ne_one : s0 ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ0 : ℝ) = 1 := by
        simpa [s0, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ0 = 0 := by linarith
      exact (ne_of_gt hδ0pos) this
    have hs0_re_gt_one : 1 < s0.re := by
      simpa [s0, Complex.add_re, Complex.ofReal_re] using by linarith
    have hζ_ne : riemannZeta s0 ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (le_of_lt hs0_re_gt_one)
    have hHs0_eq : H s0 = (s0 - 1) * riemannZeta s0 := by
      simp [H, Function.update_of_ne hs0_ne_one]
    have hHs0_ne : H s0 ≠ 0 := by
      have hs0m1_ne : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0_ne_one
      have : (s0 - 1) * riemannZeta s0 ≠ 0 := mul_ne_zero hs0m1_ne hζ_ne
      simpa [hHs0_eq] using this
                                                                                
    have hH_an_at_s0 : AnalyticAt ℂ H s0 := hH_analytic_univ s0 (by simp)
    have hH'_an_at_s0 : AnalyticAt ℂ (fun z => deriv H z) s0 := hH_an_at_s0.deriv
    have hG_an_at_s0 : AnalyticAt ℂ (fun z => G z) s0 := by
      have h_div : AnalyticAt ℂ (fun z => (deriv H z) / H z) s0 :=
        hH'_an_at_s0.div hH_an_at_s0 (by simpa using hHs0_ne)
      have h_neg : AnalyticAt ℂ (fun z => -((deriv H z) / H z)) s0 := h_div.neg
      simpa [G, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using h_neg
    have hG_cont_s0 : ContinuousAt (fun z : ℂ => G z) s0 := hG_an_at_s0.continuousAt
                                               
    let affine : ℝ → ℂ := fun δ => (1 : ℂ) + (δ : ℂ)
    have h_affine_at : ContinuousAt affine δ0 :=
      (continuousAt_const).add Complex.continuous_ofReal.continuousAt
                           
    have hy : affine δ0 = s0 := by simp [affine, s0]
    have hG_at : ContinuousAt (fun z : ℂ => G z) (affine δ0) := by simpa [hy] using hG_cont_s0
    have h_comp_at : ContinuousAt (fun δ : ℝ => G (affine δ)) δ0 := hG_at.comp h_affine_at
    simpa [F, s, affine] using h_comp_at.continuousWithinAt

  have h_eq_on_s : ∀ ⦃δ : ℝ⦄, δ ∈ s → f δ = F δ := by
    intro δ hδ
    have hδpos : 0 < δ := lt_of_lt_of_le h0 hδ.1
    simpa [f, F] using h_eq_on_pos hδpos

  have hK : IsCompact s := isCompact_Icc
  have hNorm_contOn : ContinuousOn (fun δ => ‖F δ‖) s := hF_contOn.norm
  have hBdd : BddAbove ((fun δ => ‖F δ‖) '' s) := IsCompact.bddAbove_image hK hNorm_contOn
  rcases hBdd with ⟨C, hC⟩

  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro δ hδa hδb
                                                               
  change ‖f δ‖ ≤ max C 0
  have hδmem : δ ∈ s := ⟨hδa, hδb⟩
  have himg : (fun δ => ‖F δ‖) δ ∈ (fun δ => ‖F δ‖) '' s := ⟨δ, hδmem, rfl⟩
  have hbound : ‖F δ‖ ≤ C := hC himg
  have hbound' : ‖F δ‖ ≤ max C 0 := le_trans hbound (le_max_left _ _)
                                       
  have hfδ_eq : f δ = F δ := h_eq_on_s hδmem
  calc
    ‖f δ‖ = ‖F δ‖ := by simp [hfδ_eq]
    _ ≤ max C 0 := hbound'

lemma norm_one_div_coe_real_le_one_of_one_le {δ : ℝ} (h : 1 ≤ δ) : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := by
                                                
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one h
  calc
    ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      exact norm_div (1 : ℂ) (δ : ℂ)
    _ = 1 / ‖(δ : ℂ)‖ := by simp
    _ = 1 / |δ| := by simp
    _ = 1 / δ := by simp [abs_of_nonneg (le_of_lt hδpos)]
    _ ≤ 1 := by
                                                           
      simpa using (one_div_le_one_div_of_le (ha := (zero_lt_one)) (h := h))

lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
                                                 
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
                          
  let a : ℝ := min δ0 1
  have ha_pos : 0 < a := lt_min_iff.2 ⟨hδ0pos, zero_lt_one⟩
  have ha_le_one : a ≤ 1 := min_le_right _ _
  rcases bounded_on_compact_interval a 1 ha_pos ha_le_one with ⟨Cmid, hCmid_nonneg, hmid⟩
                                                       
  let C2 : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))
  have hC2_nonneg : 0 ≤ C2 := by
    have hnn : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
      vonMangoldt_rpow_nonneg 2
    exact tsum_nonneg_of_nonneg hnn
                                                                                
  let C : ℝ := 2 + C0 + Cmid + C2
  have hCgt1 : 1 < C := by
    have : 2 ≤ 2 + C0 + Cmid + C2 := by linarith [hC0nonneg, hCmid_nonneg, hC2_nonneg]
    linarith
  refine ⟨C, hCgt1, ?_⟩
  intro δ hδpos
  by_cases hlt : δ < δ0
  ·                                        
    have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 :=
      hsmall δ hδpos hlt
             
    have hC0_le_C : C0 ≤ C := by linarith
    exact le_trans hbound hC0_le_C
  ·          
    have hge : δ0 ≤ δ := le_of_not_gt hlt
    rcases le_total δ 1 with hδle1 | hδge1
    ·                              
      have ha_le_δ : a ≤ δ := le_trans (min_le_left δ0 1) hge
      have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid :=
        hmid δ ha_le_δ hδle1
                 
      have hCmid_le_C : Cmid ≤ C := by linarith
      exact le_trans hbound hCmid_le_C
    ·                                                     
                      
      let x : ℝ := 1 + δ
      have hx1 : 1 < x := by
        have : 0 < δ := hδpos
        have : 1 < 1 + δ := lt_add_of_pos_right 1 this
        exact this
                                                           
      have h_norm_eq_abs_real : ‖-logDerivZeta (x : ℂ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| :=
        norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt x hx1
                                      
      have eqArg : ((1 : ℂ) + δ) = (x : ℂ) := by simp [x]
                                             
      have h_norm_eq_abs : ‖-logDerivZeta ((1 : ℂ) + δ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| := by
        simpa [eqArg] using h_norm_eq_abs_real
                              
      let S : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
      have hsum_nonneg : 0 ≤ S := by
        change 0 ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
        exact tsum_nonneg_of_nonneg (vonMangoldt_rpow_nonneg x)
                                                                      
      have h_norm_le_sum : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ S := by
        have : ‖-logDerivZeta ((1 : ℂ) + δ)‖ = |S| := h_norm_eq_abs
        have : |S| = S := abs_of_nonneg hsum_nonneg
        exact le_of_eq (h_norm_eq_abs.trans this)
                                                                 
      have hx_ge_two : 2 ≤ x := by
                                     
        have : 1 ≤ δ := hδge1
        have : 2 ≤ 1 + δ := by linarith
        exact this
                                                   
      have h_le_2 : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
                          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        intro n
        by_cases h0 : n = 0
        · simp [h0]
        · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
          have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hrpow : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
            rpow_neg_antitone hn' hx_ge_two
          have hΛ_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul_of_nonneg_left hrpow hΛ_nonneg
                                   
      have h_summ_x : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
        exact Rezetaseries0 x hx1
      have h_summ_2 : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Rezetaseries0 2 (by norm_num)
      have hsum_le : S ≤ C2 := by
                                                
        have h_nonneg_x : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) :=
          vonMangoldt_rpow_nonneg x
        exact tsum_le_of_nonneg_of_le h_summ_x h_summ_2 h_nonneg_x h_le_2
                                        
      have h_norm_le_C2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C2 :=
        le_trans h_norm_le_sum hsum_le
                                                                
      have h_one_div_le : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := norm_one_div_coe_real_le_one_of_one_le hδge1
      have htriangle : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖
                        ≤ ‖-logDerivZeta ((1 : ℂ) + δ)‖ + ‖(1 : ℂ) / (δ : ℂ)‖ :=
        norm_sub_le _ _
      have hlarge_bound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C2 + 1 := by
        refine le_trans htriangle ?_
        exact add_le_add h_norm_le_C2 h_one_div_le
                     
      have hC2_le_C : C2 + 1 ≤ C := by linarith
      exact le_trans hlarge_bound hC2_le_C

lemma Z0boundRe_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) ≤ C := by
                                                 
  rcases Z0bound_const with ⟨C, hCpos, hC⟩
  use C
  constructor
  · exact hCpos
  · intro δ hδ
                                                    
    have h_bound := hC δ hδ
    exact le_trans (Complex.re_le_norm _) h_bound

lemma Z0boundRe_const2 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) ≤ C := by
                                           
  rcases Z0boundRe_const with ⟨C, hC_pos, hC⟩
  use C, hC_pos
  intro δ hδ
  have h_sub_re : ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) =
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) := by
    rw [Complex.sub_re]
    rfl
  rw [← h_sub_re]
  exact hC δ hδ

lemma Z0boundRe_const3 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    (-logDerivZeta ((1 : ℂ) + δ)).re - (1 / δ) ≤ C := by
                                                                        
  rcases Z0boundRe_const2 with ⟨C, hCpos, hC⟩
  use C, hCpos
  intro δ hδ
                           
  have h := hC δ hδ
                                                                  
  have h_re_eq : (-(1 / (δ : ℂ))).re = -(1 / δ) := by
    rw [Complex.neg_re, Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_ofReal]
                                          
  rwa [h_re_eq] at h

lemma Z341bounds_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0) (_hδ1 : δ < 1), ∀ t : ℝ, 2 < |t| → ∀ σ : ℝ,
    (σ + t * Complex.I) ∈ zeroZ →
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re
    + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re
    +     (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
    ≤ 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by
                                                                                           
  rcases Z0boundRe_const3 with ⟨C0, hC0pos, hZ0⟩
  rcases Z1bound with ⟨C1, hC1pos, hZ1⟩
  rcases lem_Z2bound with ⟨C2, hC2pos, hZ2⟩

  let C := 3 * C0 + 4 * C1 + C2

  have hC_gt_one : 1 < C := by
    have h1 : 1 < C0 := hC0pos
    have h2 : 3 < 3 * C0 := by linarith [mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 3)]
    have h3 : 0 < 4 * C1 := mul_pos (by norm_num) (lt_trans zero_lt_one hC1pos)
    have h4 : 0 < C2 := lt_trans zero_lt_one hC2pos
    linarith [h2, h3, h4]

  use C
  constructor
  · exact hC_gt_one
  · intro δ hδpos hδ1 t ht σ hσ

    have hZ0_bound : (-logDerivZeta ((1 : ℂ) + δ)).re ≤ C0 + (1 / δ) := by
      have := hZ0 δ hδpos
      linarith

    have hZ1_bound : (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re ≤ -(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2) := by
      let s := σ + t * Complex.I
      have hs_mem : s ∈ zeroZ := hσ
      have hs_im : s.im = t := by simp [s]
      have hs_re : s.re = σ := by simp [s]
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      have := hZ1 δ hδ_cond t ht s ⟨hs_mem, hs_im⟩
      rw [hs_re] at this
      exact this

    have hZ2_bound : (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re ≤ C2 * Real.log (|t| + 2) := by
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      exact hZ2 t ht δ hδ_cond

    have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
      have h1 : 2 < |t| := ht
      have h2 : Real.exp 1 < 3 := lem_three_gt_e
      have he_lt_t2 : Real.exp 1 < |t| + 2 := by linarith
      have ht2_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
      exact Real.le_log_iff_exp_le ht2_pos |>.mpr (le_of_lt he_lt_t2)

    calc
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re + (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
        ≤ 3 * (C0 + (1 / δ)) + 4 * (-(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2)) + C2 * Real.log (|t| + 2) := by
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ0_bound (by norm_num)) (mul_le_mul_of_nonneg_left hZ1_bound (by norm_num))) hZ2_bound
      _ = 3 * C0 + 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + 3 * C0 + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + ((4 * C1 + C2) * Real.log (|t| + 2) + 3 * C0) := by ring
      _ ≤ 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2 + 3 * C0) * Real.log (|t| + 2) := by
                                                                           
        have hC0_pos : 0 < C0 := lt_trans zero_lt_one hC0pos
        have hC0_nonneg : 0 ≤ 3 * C0 := mul_nonneg (by norm_num) (le_of_lt hC0_pos)
        have h_absorb := absorb_pos_constant_into_log (L := Real.log (|t| + 2)) (A := 4 * C1 + C2) (c := 3 * C0) hlog_ge_one hC0_nonneg
                                                                                                               
        exact add_le_add_right h_absorb (3 / δ - 4 / (1 + δ - σ))
      _ = 3 / δ - 4 / (1 + δ - σ) + (3 * C0 + 4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by ring

def ZeroAt (σ t : ℝ) : Prop :=
  (σ + t * I) ∈ zeroZ

def Ft (σ : ℝ) : Filter ℝ :=
  (Filter.atTop ⊔ Filter.atBot) ⊓ Filter.principal {t : ℝ | ZeroAt σ t}

def Fδ : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

lemma Rezeta1zetaseries1 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + t * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) := by
                                                         
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  convert Rezeta1zetaseries (1 + delta) t h1
                                                
  simp [Complex.ofReal_add]

lemma Rezeta1zetaseries2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)) := by
                                                             
  have h1 : 1 < 1 + delta := by linarith [hdelta]
                                                                                 
  have h2 : (1 : ℂ) + delta + (2 * t) * I = (1 + delta : ℝ) + ((2 * t) : ℝ) * I := by
    simp [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  rw [h2]
  exact Rezeta1zetaseries (1 + delta) (2 * t) h1

lemma Rezeta1zetaseries0 (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
                                             
  have h_series : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re =
                  ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) :=
    Rezeta1zetaseries1 0 delta hdelta

  have h_lhs : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re = (-logDerivZeta ((1 : ℂ) + delta)).re := by
    congr 2
    simp

  have h_rhs : ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) =
               ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
    congr 1
    funext n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      rw [lem_cost0 n hn 0 rfl, mul_one]

  rw [← h_lhs, h_series, h_rhs]

lemma Z341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
     4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
     ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Rezeta1zetaseries0 delta hdelta, Rezeta1zetaseries1 t delta hdelta, Rezeta1zetaseries2 t delta hdelta]

lemma lem341seriesConv (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    Summable (fun n : ℕ =>
      3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
      4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
                                       
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  have h5 : Summable (fun n : ℕ => 3 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))) :=
    Summable.mul_left 3 h2

  have h6 : Summable (fun n : ℕ => 4 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))) :=
    Summable.mul_left 4 h3

  have h5' : Summable (fun n : ℕ => 3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) := by
    convert h5 using 1
    ext n
    ring

  have h6' : Summable (fun n : ℕ => 4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) := by
    convert h6 using 1
    ext n
    ring

  have h7 : Summable (fun n : ℕ =>
    3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
    4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    h5'.add h6'

  exact h7.add h4

lemma lem341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))
    + (4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))
    + (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)))
    = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
                                       
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  rw [← Summable.tsum_mul_left 3 h2]
  rw [← Summable.tsum_mul_left 4 h3]

  rw [← Summable.tsum_add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)]
  rw [← Summable.tsum_add]

  congr 1
  ext n
  ring

  · exact Summable.add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)
  · exact h4

lemma lem_341seriesConverge (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)))) := by
                                                                   
  have h1 : Summable (fun n : ℕ =>
    3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
    4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
    (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    lem341seriesConv t delta hdelta

  convert h1 using 1
  ext n
  ring

lemma lem_341series2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Z341series t delta hdelta]
  exact lem341series t delta hdelta

lemma lem_Lambda_pos_trig_sum (n : ℕ) (delta : ℝ) (t : ℝ) (hn : n ≥ 1) (hdelta : delta > 0) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply mul_nonneg
  ·                                                                        
    apply lem_realnx n (1 + delta) hn
                         
    linarith [hdelta]
  ·                                                                                          
    exact lem_postriglogn n hn t

lemma seriesPos {f : ℕ → ℝ} (_h_summable : Summable (fun n => if 1 ≤ n then f n else 0)) (h_nonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ f n) : 0 ≤ ∑' (n : ℕ), (if 1 ≤ n then f n else 0) := by
  apply tsum_nonneg
  intro n
  by_cases h : 1 ≤ n
  · simp [h]
    exact h_nonneg n h
  · simp [h]

lemma lem_seriespos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply tsum_nonneg
  intro n
  by_cases h : n = 0
  ·                                                            
    simp [h]
  ·                                             
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact lem_Lambda_pos_trig_sum n delta t hn hdelta

lemma Z341pos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ 3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
        4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
        (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re := by
  rw [lem_341series2 t delta hdelta]
  exact lem_seriespos t delta hdelta

lemma frac_den_increase_bound {a b c : ℝ} (hpos : 0 < a + b) (hc : 0 ≤ c) :
  4 / (a + b + c) ≤ 4 / (a + b) := by
                                           
  have hle : a + b ≤ a + b + c := by linarith
                                              
  have h1 : 1 / (a + b + c) ≤ 1 / (a + b) := by
    exact one_div_le_one_div_of_le hpos hle
                                                      
  have h4nonneg : 0 ≤ (4 : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_left h1 h4nonneg
                                                
  have hmul' : 4 * (a + b + c)⁻¹ ≤ 4 * (a + b)⁻¹ := by
    simpa [one_div] using hmul
  simpa [div_eq_mul_inv] using hmul'

lemma log_abs_add_two_pos (t : ℝ) : 0 < Real.log (abs t + 2) := by
                                                    
  have h0 : 0 ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    linarith
  have hge : (2 : ℝ) ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    have := add_le_add_left h' (2 : ℝ)
    simp
  have hgt : 1 < abs t + 2 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hge
                                                                
  exact (Real.log_pos_iff h0).2 hgt

lemma log_gt_of_gt_exp {x y : ℝ} (h : Real.exp y < x) : y < Real.log x := by
  have hxpos : 0 < x := lt_trans (Real.exp_pos y) h
  exact (Real.lt_log_iff_exp_lt hxpos).2 h

lemma denom_rewrite (σ C L : ℝ) : 1 - σ + (1 / (2 * C * L)) = 1 + (1 / (2 * C * L)) - σ := by
  ring

lemma pos_delta_from_C_L {C L : ℝ} (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  have hCL : 0 < C * L := mul_pos hC hL
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hpos : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos h2 hCL
    simpa [mul_assoc] using this
  exact one_div_pos.mpr hpos

lemma add_two_pos_of_abs (t : ℝ) : 0 < |t| + 2 := by
  have : 0 ≤ |t| := abs_nonneg t
  linarith

lemma log_abs_two_pos (t : ℝ) : 0 < Real.log (|t| + 2) := by
  simpa using log_abs_add_two_pos t

lemma two_C_log_pos {C t : ℝ} (hC : 0 < C) : 0 < 2 * C * Real.log (|t| + 2) := by
  have hL : 0 < Real.log (|t| + 2) := log_abs_two_pos t
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hCL : 0 < C * Real.log (|t| + 2) := mul_pos hC hL
  have : 0 < 2 * (C * Real.log (|t| + 2)) := mul_pos h2 hCL
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma mul_one_div_self_of_pos {a : ℝ} (ha : 0 < a) : a * (1 / a) = 1 := by
  have hne : a ≠ 0 := ne_of_gt ha
  simp [one_div, hne]

lemma mul_one_div_mul_right {A b : ℝ} (hA : A ≠ 0) : A * (1 / (A * b)) = 1 / b := by
  calc
    A * (1 / (A * b)) = A * ((A * b)⁻¹) := by simp [one_div]
    _ = A / (A * b) := by simp [div_eq_mul_inv]
    _ = A / A / b := by
      simpa using (div_mul_eq_div_div (a := A) (b := A) (c := b))
    _ = 1 / b := by
      have : A / A = (1 : ℝ) := by simp [hA]
      simp [this]

lemma one_div_mul_one_div_mul_right {A b : ℝ} (hA : A ≠ 0) (_hb : b ≠ 0) : 1 / (A * (1 / (A * b))) = b := by
  have h := mul_one_div_mul_right (A := A) (b := b) hA
  have hinv := congrArg (fun x : ℝ => x⁻¹) h
  calc
    1 / (A * (1 / (A * b))) = (A * (1 / (A * b)))⁻¹ := by simp [one_div]
    _ = (1 / b)⁻¹ := by simpa using hinv
    _ = b := by simp [one_div]

lemma inv_of_delta_def (C L δ : ℝ) (hδ : δ = 1 / (2 * C * L)) : 1 / δ = 2 * C * L := by
  simp [hδ, one_div]

lemma rhs_eval_of_inv (C L δ : ℝ) (h : 1 / δ = 2 * C * L) : 3 / δ + C * L = 7 * C * L := by
  calc
    3 / δ + C * L
        = 3 * (1 / δ) + C * L := by simp [div_eq_mul_inv]
    _   = 3 * (2 * C * L) + C * L := by simp [h]
    _   = 6 * C * L + C * L := by ring
    _   = 7 * C * L := by ring

lemma lem341tsC :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    4 / (1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2))) ≤ 7 * C * Real.log (abs s.im + 2) := by
                                             
  obtain ⟨C, hCpos, hbound⟩ := Z341bounds_const
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTim

  let L : ℝ := Real.log (|s.im| + 2)
  have hLpos : 0 < L := log_abs_two_pos (s.im)
  let δ : ℝ := 1 / (2 * C * L)

  have hCpos_weak : 0 < C := lt_trans zero_lt_one hCpos
  have hδpos : 0 < δ := pos_delta_from_C_L hCpos_weak hLpos

  have hδlt : δ < 1 := by
                                               
    have hL_gt_1 : 1 < L := by
      have h5_lt : 4 < |s.im| + 2 := by linarith [hTim]
      have hL_gt_log5 : Real.log 4 < L := Real.log_lt_log (by norm_num) h5_lt
      have hlog5_gt_1 : 1 < Real.log 4 := by
        have h5_gt_e : Real.exp 1 < 4 := by
          have h3_gt_e := lem_three_gt_e
          linarith [h3_gt_e]
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) h5_gt_e
      linarith [hlog5_gt_1, hL_gt_log5]
                                                      
    have h2CL_gt_1 : 1 < 2 * C * L := by
                                                                             
      have hCL_gt_1 : 1 < C * L := by
        calc C * L
          > 1 * L := by exact mul_lt_mul_of_pos_right hCpos hLpos
          _ = L := by simp
          _ > 1 := hL_gt_1
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      calc 2 * C * L
        = 2 * (C * L) := by ring
        _ > 2 * 1 := by exact mul_lt_mul_of_pos_left hCL_gt_1 h2_pos
        _ = 2 := by simp
        _ > 1 := by norm_num
                                  
    simp only [δ]
    rw [div_lt_one_iff]
    left
    exact ⟨two_C_log_pos hCpos_weak, h2CL_gt_1⟩

  have hmem : (s.re + s.im * Complex.I) ∈ zeroZ := by
    simpa [Complex.re_add_im] using hs.1
  have hupper := hbound δ hδpos hδlt (s.im) hTim (s.re) hmem

  have hpos := Z341pos (s.im) δ hδpos

  have hRHS_nonneg : 0 ≤ 3 / δ - 4 / (1 + δ - s.re) + C * L := le_trans hpos hupper
  have hineq1 : 4 / (1 + δ - s.re) ≤ 3 / δ + C * L := by linarith [hRHS_nonneg]

  have hineq2 : 4 / (1 - s.re + δ) ≤ 3 / δ + C * L := by
    convert hineq1 using 2
    ring

  have hinv : 1 / δ = 2 * C * L := by
    simp only [δ, one_div, inv_inv]

  have hrhs_eval : 3 / δ + C * L = 7 * C * L := rhs_eval_of_inv C L δ hinv

  have hfinal : 4 / (1 - s.re + δ) ≤ 7 * C * L := by
    rw [← hrhs_eval]
    exact hineq2

  convert hfinal

lemma zeta_zero_re_lt_one (s : ℂ) (hs : s ∈ zeroZ) : s.re < 1 := by
                           
  by_contra h
                                        
  push Not at h

  have h_zero : riemannZeta s = 0 := hs
                                                                                
  have h_nonzero : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h
                                  
  exact h_nonzero h_zero

lemma div_le_to_le_mul (x y z : ℝ) (hy : 0 < y) (h : x / y ≤ z) : x ≤ z * y := by
  rwa [div_le_iff₀ hy] at h

lemma le_mul_to_le_div (x y z : ℝ) (hy : 0 < y) (h : x ≤ z * y) : x / y ≤ z := by
  rw [div_le_iff₀ hy]
  exact h

lemma reciprocal_div_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 4 / a ≤ b) : a ≥ 4 / b := by
                                                                
  have h1 : 4 ≤ b * a := div_le_to_le_mul 4 a b ha h
                                       
  have h2 : 4 ≤ a * b := by
    rwa [mul_comm] at h1
                                                              
  have h3 : 4 / b ≤ a := le_mul_to_le_div 4 b a hb h2
                                                                           
  exact h3

lemma lem341tsC2 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
          1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) ≥ 4 / (7 * C * Real.log (abs s.im + 2)) := by
                                                 
  rcases lem341tsC with ⟨C, hCpos, hT⟩
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTs
                                                      
  set a := 1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) with ha
  set b := 7 * C * Real.log (abs s.im + 2) with hb
  have hineq : 4 / a ≤ b := by
    simpa [ha, hb] using hT s hs hTs
                  
  have h_abs_nonneg : 0 ≤ |s.im| := abs_nonneg _
  have h_two_le : (2 : ℝ) ≤ |s.im| + 2 := by
    have h' : (2 : ℝ) + 0 ≤ 2 + |s.im| := add_le_add_right h_abs_nonneg 2
    simp
  have h_one_lt : (1 : ℝ) < |s.im| + 2 := lt_of_lt_of_le one_lt_two h_two_le
  have hx0 : 0 ≤ |s.im| + 2 := by linarith [h_abs_nonneg]
  have hlogpos : 0 < Real.log (|s.im| + 2) := (Real.log_pos_iff hx0).2 h_one_lt
  have h7pos : 0 < (7 : ℝ) := by exact_mod_cast (by decide : (0 : ℕ) < 7)
  have hbpos : 0 < b := by
    have h7Cpos : 0 < 7 * C := by linarith
    exact mul_pos h7Cpos hlogpos
                  
  rcases hs with ⟨_, hRepos, hRelt⟩
  have h1 : 0 < 1 - s.re := sub_pos.mpr hRelt
  have h2pos : 0 < (2 : ℝ) := lt_trans zero_lt_one one_lt_two
  have h2Cpos : 0 < (2 : ℝ) * C := by linarith
  have hdenpos : 0 < 2 * C * Real.log (|s.im| + 2) := mul_pos h2Cpos hlogpos
  have hinvpos : 0 < 1 / (2 * C * Real.log (|s.im| + 2)) := one_div_pos.mpr hdenpos
  have hapos : 0 < a := by
    have := add_pos h1 hinvpos
    simpa [ha] using this
                                                           
  have hres := reciprocal_div_inequality a b hapos hbpos hineq
  simpa [ha, hb] using hres

lemma simplify_4_7_2 (C L : ℝ) : 4 / (7 * C * L) - 1 / (2 * C * L) = 1 / (14 * C * L) := by
                                             
  have h1 : (4 : ℝ) / (7 * (C * L)) = (4 : ℝ) / (7 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (4 : ℝ)) (b := (7 : ℝ)) (c := C * L))
  have h2 : (1 : ℝ) / (2 * (C * L)) = (1 : ℝ) / (2 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (1 : ℝ)) (b := (2 : ℝ)) (c := C * L))
                                                     
  have h3' : ((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹ = (14 : ℝ)⁻¹ := by
    have h3 : ((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (14 : ℝ) := by
      norm_num
    simpa [one_div] using h3
  calc
    4 / (7 * C * L) - 1 / (2 * C * L)
        = (4 : ℝ) / (7 * (C * L)) - (1 : ℝ) / (2 * (C * L)) := by
          simp [mul_assoc]
    _ = (4 : ℝ) / (7 : ℝ) / (C * L) - (1 : ℝ) / (2 : ℝ) / (C * L) := by
          simp [h1, h2]
    _ = (((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ))) / (C * L) := by
          simpa using (sub_div (a := ((4 : ℝ) / (7 : ℝ))) (b := ((1 : ℝ) / (2 : ℝ))) (c := C * L)).symm
    _ = (((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹) / (C * L) := by
          simp [one_div]
    _ = (14 : ℝ)⁻¹ / (C * L) := by
          simp [h3']
    _ = 1 / (14 * (C * L)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using
            (div_mul_eq_div_div (a := (1 : ℝ)) (b := (14 : ℝ)) (c := C * L)).symm
    _ = 1 / (14 * C * L) := by simp [mul_assoc]

lemma fraction_diff_lower_bound (C L a : ℝ) : 4 / (7 * C * L) ≤ a + 1 / (2 * C * L) → 1 / (14 * C * L) ≤ a := by
  intro h
  have h' : 4 / (7 * C * L) - 1 / (2 * C * L) ≤ a := (sub_le_iff_le_add).mpr h
  have hdiff : 1 / (14 * C * L) = 4 / (7 * C * L) - 1 / (2 * C * L) := by
    symm
    exact simplify_4_7_2 C L
  calc
    1 / (14 * C * L)
        = 4 / (7 * C * L) - 1 / (2 * C * L) := hdiff
    _ ≤ a := h'

lemma lem341tsC3 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    1 - s.re ≥ 1 / (14 * C * Real.log (abs s.im + 2)) := by
  obtain ⟨C, hCpos, hT⟩ := lem341tsC2
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTle
  have h := hT s hs hTle
                                                                             
  have h' : 4 / (7 * C * Real.log (abs s.im + 2)) ≤
      (1 - s.re) + 1 / (2 * C * Real.log (abs s.im + 2)) := by
    simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using h
                                            
  have h'' := fraction_diff_lower_bound C (Real.log (abs s.im + 2)) (1 - s.re) h'
             
  simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using h''

lemma zerofree :
    ∃ c, c > 0 ∧ c < 1 ∧ ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| → s.re ≤ 1 - c / (Real.log (abs s.im + 2)) := by
                                          
  rcases lem341tsC3 with ⟨C0, hC0pos, hT⟩
                                                 
  set C : ℝ := 1 / (14 * C0) with hCdef
               
  have h14pos : 0 < (14 : ℝ) := by norm_num
  have hC0pos' : 0 < C0 := lt_trans zero_lt_one hC0pos
  have hCpos : 0 < C := by
    have hdenpos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    exact one_div_pos.mpr hdenpos
                                                                             
  have hClt1 : C < 1 := by
    have h14C0_pos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    have h14C0_gt_1 : 1 < 14 * C0 := by
      have h14_gt_1 : (1 : ℝ) < 14 := by norm_num
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < 14 * 1 := by exact mul_lt_mul_of_pos_right h14_gt_1 zero_lt_one
        _ < 14 * C0 := by exact mul_lt_mul_of_pos_left hC0pos h14pos
    rw [hCdef]
    rw [div_lt_one_iff]
    left
    exact ⟨h14C0_pos, h14C0_gt_1⟩
                                                  
  refine ⟨C, hCpos, hClt1, ?_⟩
  intro s hs hTle
                                    
  set L := Real.log (abs s.im + 2) with hLdef
                                                          
  have hb0 := hT s hs hTle
                                                 
  have hb' : C / L ≤ 1 - s.re := by
    simpa [hLdef, hCdef, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb0
                                             
  have : s.re ≤ 1 - C / L := by linarith
  simpa [hLdef] using this

def Yt (t : ℝ) (δ : ℝ) : Set ℂ :=
  { ρ_1 : ℂ | riemannZeta ρ_1 = 0 ∧ ‖ρ_1 - (1 - δ + t * Complex.I)‖ ≤ 2 * δ }

noncomputable def zerofree_constant : ℝ := Classical.choose zerofree

lemma zerofree_constant_pos : 0 < zerofree_constant :=
  (Classical.choose_spec zerofree).1

lemma zerofree_constant_lt_one : zerofree_constant < 1 :=
  (Classical.choose_spec zerofree).2.1

noncomputable def deltaz (z : ℂ) : ℝ := (zerofree_constant / 20) / Real.log (|z.im| + 2)

noncomputable def deltaz_t (t : ℝ) : ℝ := deltaz (t * Complex.I)

lemma lem_delta19 :
  (∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9)) ∧
  (∀ t : ℝ, |t| > 2 → (0 < deltaz_t t ∧ deltaz_t t < 1/9)) := by
                                          
  have h_complex : ∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9) := by
    intro z hz
    constructor
    ·                     
      have h_num_pos : 0 < zerofree_constant / 20 := by
        exact div_pos zerofree_constant_pos (by norm_num)
      have h_den_pos : 0 < Real.log (|z.im| + 2) := by
        have h_gt_one : (1 : ℝ) < |z.im| + 2 := by
          have h_nonneg : (0 : ℝ) ≤ |z.im| := abs_nonneg _
          linarith [hz]
        exact Real.log_pos h_gt_one
      unfold deltaz
      exact div_pos h_num_pos h_den_pos
    ·                       
                                       
      have h_den_ge_half : (1/2 : ℝ) ≤ Real.log (|z.im| + 2) := by
                                         
        have h_den_ge_log2 : Real.log 2 ≤ Real.log (|z.im| + 2) := by
          have h_pos : 0 < |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          have h_le : (2 : ℝ) ≤ |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          exact Real.log_le_log (by norm_num) h_le
                                              
        have h_log2_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
          have h_exp_half_le_two : Real.exp (1/2) ≤ 2 := by
                                                                 
            have h_exp_one_lt_three : Real.exp 1 < 3 := lem_three_gt_e
            have h_exp_sq : (Real.exp (1/2))^2 = Real.exp 1 := by
              rw [pow_two, ← Real.exp_add]; norm_num
            have h_exp_sq_lt_four : (Real.exp (1/2))^2 < 4 := by
              rw [h_exp_sq]; linarith [h_exp_one_lt_three]
                                               
            have h_exp_pos : 0 ≤ Real.exp (1/2) := le_of_lt (Real.exp_pos _)
            have h_two_pos : 0 ≤ (2 : ℝ) := by norm_num
            have h_four_eq : (2 : ℝ)^2 = 4 := by norm_num
            rw [← h_four_eq] at h_exp_sq_lt_four
            have h_lt_abs := (sq_lt_sq).mp h_exp_sq_lt_four
            rw [abs_of_nonneg h_exp_pos, abs_of_nonneg h_two_pos] at h_lt_abs
            exact le_of_lt h_lt_abs
          exact (Real.le_log_iff_exp_le (by norm_num : 0 < (2 : ℝ))).mpr h_exp_half_le_two
        exact le_trans h_log2_ge_half h_den_ge_log2
                                            
      have h_inv_le_two : 1 / Real.log (|z.im| + 2) ≤ 2 := by
        have h_pos_half : 0 < (1/2 : ℝ) := by norm_num
        have h_ineq := one_div_le_one_div_of_le h_pos_half h_den_ge_half
        convert h_ineq using 1; first | rfl | norm_num
                           
      have h_bound : deltaz z ≤ zerofree_constant / 10 := by
        unfold deltaz

        rw [div_eq_mul_inv]
                                                                                              
        have h_num_nonneg : 0 ≤ zerofree_constant / 20 := by
          exact le_of_lt (div_pos zerofree_constant_pos (by norm_num))
        have h_mul_ineq := mul_le_mul_of_nonneg_left h_inv_le_two h_num_nonneg
        convert h_mul_ineq using 1 <;> first | rfl | ring
                                                         
      have h_lt_tenth : zerofree_constant / 10 < 1 / 10 := by
        exact div_lt_div_of_pos_right zerofree_constant_lt_one (by norm_num)
      have h_tenth_lt_ninth : (1 : ℝ) / 10 < 1 / 9 := by norm_num
      exact lt_trans (lt_of_le_of_lt h_bound h_lt_tenth) h_tenth_lt_ninth

  constructor
  · exact h_complex
  ·              
    intro t ht
                                                                             
    have h_eq : deltaz_t t = deltaz (t * Complex.I) := rfl
    rw [h_eq]
    have h_im_eq : |(t * Complex.I).im| = |t| := by simp
    rw [← h_im_eq] at ht
    exact h_complex (t * Complex.I) ht

lemma closedBall_compact_complex (c : ℂ) (r : ℝ) :
    IsCompact (Metric.closedBall c r) := by
                                                                           
  exact ProperSpace.isCompact_closedBall c r

lemma riemannZeta_no_zeros_accumulate_at_one :
  ∀ Z : Set ℂ, (∀ z ∈ Z, riemannZeta z = 0) → ¬AccPt 1 (Filter.principal Z) := by
  intro Z hZ
                           
  by_contra h_acc

  have h_residue := riemannZeta_residue_one

  rw [Metric.tendsto_nhdsWithin_nhds] at h_residue
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_residue (1/2) (by norm_num : (0 : ℝ) < 1/2)

  rw [accPt_iff_nhds] at h_acc

  obtain ⟨y, ⟨hy_ball, hy_Z⟩, hy_ne⟩ := h_acc (Metric.ball 1 δ) (Metric.ball_mem_nhds 1 hδ_pos)

  have hy_zero : riemannZeta y = 0 := hZ y hy_Z

  have hy_in_compl : y ∈ ({1} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hy_ne

  have hy_dist : dist y 1 < δ := hy_ball

  have h_bound := hδ_bound hy_in_compl hy_dist

  rw [hy_zero, mul_zero] at h_bound

  have h_dist_eq : dist (0 : ℂ) (1 : ℂ) = 1 := by
    rw [Complex.dist_eq]
    norm_num

  rw [h_dist_eq] at h_bound
                                                 
  norm_num at h_bound

lemma complex_minus_singleton_connected : IsPreconnected ({s : ℂ | s ≠ 1} : Set ℂ) := by
                                                                   
  have h_eq : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext x
    simp [Set.mem_compl_iff, Set.mem_singleton_iff]

  rw [h_eq]

  have h_rank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
                                         
    norm_num

  have h_connected := isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)

  exact h_connected.isPreconnected

lemma eventually_eq_zero_implies_frequently_eq_zero_punctured (f : ℂ → ℂ) (z₀ : ℂ) :
  (∀ᶠ z in nhds z₀, f z = 0) → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0) := by
  intro h_eventually

  have h_nebot : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := by
                                                                                
    exact NormedField.nhdsNE_neBot z₀

  have h_eventually_punctured : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0 := by
                                                        
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h_eventually

  exact h_eventually_punctured.frequently

lemma riemannZeta_zeros_finite_of_compact (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by

  by_contra h_not_finite
  push Not at h_not_finite

  let Z := {z ∈ K | riemannZeta z = 0}

  have hZ_inf : Z.Infinite := h_not_finite
  have hZ_sub : Z ⊆ K := fun z hz => hz.1

  obtain ⟨z₀, hz₀_K, hz₀_acc⟩ := lem_bolzano_weierstrass hK hZ_inf hZ_sub

  by_cases h_eq_one : z₀ = 1
  ·                                                               
    subst h_eq_one
                                                 
    have hZ_zeros : ∀ z ∈ Z, riemannZeta z = 0 := fun z hz => hz.2
                                                              
    exact riemannZeta_no_zeros_accumulate_at_one Z hZ_zeros hz₀_acc

  ·                                    
                                                                 
    have h_analytic : AnalyticAt ℂ riemannZeta z₀ :=
      zetaanalOnnot1 z₀ h_eq_one

    obtain h_ev_zero | h_ev_ne := h_analytic.eventually_eq_zero_or_eventually_ne_zero

    ·                                                                

      have h_freq := eventually_eq_zero_implies_frequently_eq_zero_punctured riemannZeta z₀ h_ev_zero

      have h_eq_on_zero := zetaanalOnnot1.eqOn_zero_of_preconnected_of_frequently_eq_zero
        complex_minus_singleton_connected h_eq_one h_freq

      have : riemannZeta 0 = 0 := h_eq_on_zero (by simp : (0 : ℂ) ∈ {s | s ≠ 1})
      rw [riemannZeta_zero] at this
      norm_num at this

    ·                                                                       

      unfold AccPt at hz₀_acc

      have h_ev_not_Z : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ∉ Z := by
        apply Filter.Eventually.mono h_ev_ne
        intro z hz hz_in_Z
        exact hz hz_in_Z.2

      have h_ev_false : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z, False := by
        rw [Filter.eventually_inf_principal]
        exact h_ev_not_Z

      have h_eq_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z = ⊥ :=
        Filter.eventually_false_iff_eq_bot.mp h_ev_false

      have h_ne_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z ≠ ⊥ := hz₀_acc.ne

      exact h_ne_bot h_eq_bot

lemma lem_ZFRdelta :
  ∀ z : ℂ, 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0 := by
  intro z him hre
  by_cases h1 : 1 ≤ z.re
  ·                                     
    simpa using riemannZeta_ne_zero_of_one_le_re h1
                        
  have hzlt1 : z.re < 1 := lt_of_not_ge h1
                                                 
  have hgt : |z.im| > 2 := by simpa using him
  have hδ := (lem_delta19).1 z hgt
  rcases hδ with ⟨hδ_pos, hδ_lt_19⟩
                                                                  
  have h9δ_lt1 : 9 * deltaz z < 1 := by
    have h := mul_lt_mul_of_pos_left hδ_lt_19 (by norm_num : 0 < (9 : ℝ))
    have h9 : (9 : ℝ) * (1 / 9) = 1 := by norm_num
    simpa [h9] using h
  have hzre_pos : 0 < z.re := by
    have : 0 < 1 - 9 * deltaz z := sub_pos.mpr h9δ_lt1
    exact lt_trans this hre
                                           
  by_contra hzero
  have hzmem : z ∈ zeroZ := by simpa [zeroZ] using hzero
                                                                   
  have hprop := (Classical.choose_spec zerofree).2.2
  have hbound : z.re ≤ 1 - zerofree_constant / Real.log (|z.im| + 2) :=
    hprop z ⟨hzmem, hzre_pos, hzlt1⟩ him
                                           
  set L : ℝ := Real.log (|z.im| + 2) with hLdef
  have hLpos : 0 < L := by
    have hone_lt : (1 : ℝ) < |z.im| + 2 := by
      have : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      linarith
    have := Real.log_pos hone_lt
    simpa [hLdef] using this
                                     
  have hb_le_a' : ((9 : ℝ) / 20) * (zerofree_constant / L) ≤ zerofree_constant / L := by
    have hcoef_le1 : ((9 : ℝ) / 20) ≤ 1 := by norm_num
    have ha_nonneg : 0 ≤ zerofree_constant / L := le_of_lt (div_pos zerofree_constant_pos hLpos)
    have := mul_le_mul_of_nonneg_right hcoef_le1 ha_nonneg
    simpa [one_mul] using this
  have h9d_eq : 9 * deltaz z = ((9 : ℝ) / 20) * (zerofree_constant / L) := by
    simp [deltaz, hLdef, div_eq_mul_inv, mul_left_comm, mul_assoc]
  have hdelta_le : 9 * deltaz z ≤ zerofree_constant / L := by
    simpa [h9d_eq] using hb_le_a'
  have h_le_rhs : 1 - zerofree_constant / L ≤ 1 - 9 * deltaz z := by
    have hneg := neg_le_neg hdelta_le
    simpa [sub_eq_add_neg] using! add_le_add_right hneg 1
                              
  have hle : z.re ≤ 1 - 9 * deltaz z := le_trans hbound h_le_rhs
  have hcontr : z.re < z.re := lt_of_le_of_lt hle hre
  exact (lt_irrefl (z.re)) hcontr

lemma complex_re_add_I_mul_real (a t : ℝ) : (((a : ℂ) + Complex.I * t).re) = a := by
                                                                 
  have h1 : ((Complex.I * (t : ℂ)).re) = -((t : ℂ).im) := by
    simp
  have ht_im : ((t : ℂ).im) = 0 := by simp
  simp [Complex.add_re, Complex.ofReal_re, h1]

lemma complex_im_add_I_mul_real (a t : ℝ) : (((a : ℂ) + Complex.I * t).im) = t := by
                                                            
  have h1 : ((Complex.I * (t : ℂ)).im) = ((t : ℂ).re) := by
    simp
  have ht_re : ((t : ℂ).re) = t := by simp
  simp [Complex.add_im, Complex.ofReal_im, h1]

lemma complex_sub_ofReal_I_real_eq_ofReal (z : ℂ) (a t : ℝ) (him : z.im = t) :
  z - ((a : ℂ) + Complex.I * t) = ((z.re - a) : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, him]

lemma lem_ZFRinD (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∈ Metric.closedBall c (2/3) := by
  intro c h
  rcases h with ⟨h_low, hrest⟩
  rcases hrest with ⟨h_high, him⟩
  have hsub : z - c = ((z.re - (3/2)) : ℂ) := by
    simpa [c] using! complex_sub_ofReal_I_real_eq_ofReal z (3/2) t him
  have h1 : dist z c = ‖((z.re - (3/2)) : ℂ)‖ := by
    simp [dist_eq_norm, hsub]
  have h2 : ‖((z.re - (3/2)) : ℂ)‖ = ‖z.re - (3/2)‖ := by
    simpa using (Complex.norm_real (z.re - (3/2)))
  have hdist_abs : dist z c = |z.re - (3/2)| := by
    have h4 : dist z c = ‖z.re - (3/2)‖ := h1.trans h2
    simpa [Real.norm_eq_abs] using h4
  have hnonpos : z.re - (3/2) ≤ 0 := sub_nonpos_of_le h_high
  have habs : |z.re - (3/2)| = 3/2 - z.re := by
    have := abs_of_nonpos hnonpos
    simpa [neg_sub] using this
  have hdist_eq : dist z c = 3/2 - z.re := hdist_abs.trans habs
  have h_le : dist z c ≤ 1/2 + deltaz_t t := by
    calc
      dist z c = 3/2 - z.re := hdist_eq
      _ ≤ 3/2 - (1 - deltaz_t t) := by linarith
      _ = 1/2 + deltaz_t t := by ring
  have hδlt : deltaz_t t < 1/9 := (lem_delta19.2 t ht).2
  have h12δ_lt : (1/2 : ℝ) + deltaz_t t < (1/2 : ℝ) + 1/9 := by
    have := add_lt_add_left hδlt (1/2 : ℝ)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have h123_lt : (1/2 : ℝ) + 1/9 < (2/3 : ℝ) := by norm_num
  have h_lt : (1/2 : ℝ) + deltaz_t t < (2/3 : ℝ) := lt_trans h12δ_lt h123_lt
  have hdist_le : dist z c ≤ 2/3 := le_trans h_le (le_of_lt h_lt)
  exact (Metric.mem_closedBall).2 hdist_le

lemma lem_ZFRnotK (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∉ zerosetKfRc (5/6) c riemannZeta := by
  intro c h

  obtain ⟨h_ge, h_le, h_im⟩ := h

  have h_delta_eq : deltaz z = deltaz_t t := by
    rw [deltaz_t, deltaz]
                                              
    congr 1
    congr 1
                                         
    rw [h_im]

    simp only [Complex.mul_I_im, Complex.ofReal_re]

  have h_ge_delta : 1 - deltaz z ≤ Complex.re z := by
    rwa [← h_delta_eq] at h_ge

  have h_im_gt : |z.im| > 2 := by
    rw [h_im]
    exact ht

  have h_delta_pos : 0 < deltaz z := by
    exact (lem_delta19.1 z h_im_gt).1

  have h_delta_lt_9delta : deltaz z < 9 * deltaz z := by
    linarith [h_delta_pos]

  have h_strict : Complex.re z > 1 - 9 * deltaz z := by
    linarith [h_ge_delta, h_delta_lt_9delta]

  have h_zeta_ne_zero : riemannZeta z ≠ 0 :=
    lem_ZFRdelta z h_im_gt h_strict

  intro h_mem
                                                                  
  have h_zero : riemannZeta z = 0 := h_mem.2
                                    
  exact h_zeta_ne_zero h_zero

lemma lem_Zeta_Expansion_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t;
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
        ‖(deriv riemannZeta z / riemannZeta z) -
          (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖
        ≤ C_1 * Real.log |t| := by
  obtain ⟨C, hC_gt_one, hC_expansion⟩ :=
    Zeta1_Zeta_Expansion (2/3) (3/4)
    (by norm_num : (0 : ℝ) < 2/3)
    (by norm_num : (2/3 : ℝ) < 3/4)
    (by norm_num : (3/4 : ℝ) < 5/6)
  let C_1 := C * (1 / ((3/4 : ℝ) - 2/3)^3 + 1)
  have hC_1_gt_1 : C_1 > 1 := by
    have h_coeff : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 + 1 > 1 := by
      have h_pos : ((3/4 : ℝ) - 2/3)^3 > 0 := by norm_num
      have h_div_pos : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 > 0 := div_pos one_pos h_pos
      linarith
    have h_ge_1 : (1 : ℝ) ≤ C := le_of_lt hC_gt_one
    exact one_lt_mul_of_le_of_lt h_ge_1 h_coeff
  refine ⟨C_1, hC_1_gt_1, ?_⟩
  intro t ht c hfin z hz
  have ht2 : |t| > 2 := by linarith
  have hz_in_ball : z ∈ Metric.closedBall c (2/3) := by
    simpa [c] using (lem_ZFRinD t ht2 z hz)
  have hz_not_in_K : z ∉ zerosetKfRc (5/6) c riemannZeta := by
    simpa [c] using (lem_ZFRnotK t ht2 z hz)
  have hz_in_diff : z ∈ Metric.closedBall c (2/3) \ zerosetKfRc (5/6) c riemannZeta :=
    ⟨hz_in_ball, hz_not_in_K⟩
  have h_expansion := hC_expansion t ht hfin z hz_in_diff
  rw [show logDerivZeta z = deriv riemannZeta z / riemannZeta z from rfl] at h_expansion
  exact h_expansion

lemma lem_abszrhoReRe (z ρ : ℂ) : ‖z - ρ‖ ≥ z.re - ρ.re := by
  have h1 : (z - ρ).re ≤ ‖z - ρ‖ := Complex.re_le_norm (z - ρ)
  have h2 : (z - ρ).re = z.re - ρ.re := Complex.sub_re z ρ
  rw [← h2]
  exact h1

lemma lem_Rerhotodeltarho {ρ : ℂ} :
  ∀ t : ℝ, |t| > 3 → ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) (3/2+ t* Complex.I) riemannZeta) → ρ.re ≤ 1 - 9 * deltaz ρ := by
  intro t ht h_mem
                                                   
  have h_zero : riemannZeta ρ = 0 := h_mem.2

  have h_ball : ρ ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6) := h_mem.1

  have h_dist : dist ρ (3/2 + t * Complex.I) ≤ 5/6 := by
    rwa [Metric.mem_closedBall] at h_ball

  have h_im : 2 < |ρ.im| := by
                                                                 
    have h_im_bound : |ρ.im - t| ≤ 5/6 := by
                                         
      have h_le_norm : |ρ.im - t| ≤ ‖ρ - (3/2 + t * Complex.I)‖ := by
        have : |(ρ - (3/2 + t * Complex.I)).im| ≤ ‖ρ - (3/2 + t * Complex.I)‖ :=
          Complex.abs_im_le_norm _
        have h_im_eq : (ρ - (3/2 + t * Complex.I)).im = ρ.im - t := by
          simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im]
        rwa [← h_im_eq]
      rw [← Complex.dist_eq] at h_le_norm
      linarith [h_le_norm, h_dist]

    have triangle := abs_sub_abs_le_abs_sub t ρ.im

    have eq_comm : |t - ρ.im| = |ρ.im - t| := abs_sub_comm t ρ.im
    rw [eq_comm] at triangle

    have h_ge : |ρ.im| ≥ |t| - |ρ.im - t| := by linarith [triangle]

    have : |ρ.im| ≥ |t| - 5/6 := by linarith [h_ge, h_im_bound]
    have : |ρ.im| > 3 - 5/6 := by linarith [ht]
    have h_calc : (3 : ℝ) - 5/6 = 13/6 := by norm_num
    have h_gt2 : (13 : ℝ)/6 > 2 := by norm_num
    rw [h_calc] at *
    linarith [h_gt2]

  have h_not_gt : ¬(ρ.re > 1 - 9 * deltaz ρ) := by
    intro h_gt
    have h_ne_zero := lem_ZFRdelta ρ h_im h_gt
    exact h_ne_zero h_zero

  exact le_of_not_gt h_not_gt

lemma lem_DImt2d :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| ≤ |t| + 5/6 := by
  intro t ht z hz
                                                                  
  rw [Metric.mem_closedBall] at hz
                                    
  have center_im : (3/2 + t * Complex.I).im = t := by simp [Complex.add_im, Complex.mul_im]
                                  
  have diff_im : (z - (3/2 + t * Complex.I)).im = z.im - t := by
    rw [Complex.sub_im, center_im]
                                      
  have h1 : |z.im - t| ≤ ‖z - (3/2 + t * Complex.I)‖ := by
    rw [← diff_im]
    exact Complex.abs_im_le_norm _
                                       
  have h2 : |z.im - t| ≤ 5/6 := le_trans h1 (by simpa only [dist_eq_norm] using! hz)
                                                                                            
  have h3 : |z.im| ≤ |z.im - t| + |t| := by
    conv_lhs => rw [show z.im = (z.im - t) + t by ring]
    exact abs_add_le (z.im - t) t
  linarith

lemma lem_DIMt2 :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| + 2 ≤ (|t| + 2)^3 := by
  intro t ht z hz
                                                
  have h1' := lem_DImt2d t ht z hz
                                     
  have h1a : |z.im| + 2 ≤ |t| + 17/6 := by
    simpa [show |t| + 5/6 + 2 = |t| + 17/6 by ring] using! add_le_add_left h1' 2
                                
  have h17le3 : |t| + 17/6 ≤ |t| + 3 := by
    have : (17 : ℝ) / 6 ≤ 3 := by norm_num
    exact add_le_add_right this _
                                                                    
  have h_nonneg_poly : 0 ≤ |t|^3 + 6 * |t|^2 + 11 * |t| + 5 := by
    have h0 : 0 ≤ |t|^3 := by exact pow_nonneg (abs_nonneg _) 3
    have h1 : 0 ≤ 6 * |t|^2 := by
      have : 0 ≤ (6 : ℝ) := by norm_num
      exact mul_nonneg this (sq_nonneg _)
    have h2 : 0 ≤ 11 * |t| := by
      have : 0 ≤ (11 : ℝ) := by norm_num
      exact mul_nonneg this (abs_nonneg _)
    have h3 : 0 ≤ (5 : ℝ) := by norm_num
    exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3
  have h_add : |t| + 3 ≤ (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    simpa using (le_add_of_nonneg_right (a := |t| + 3) h_nonneg_poly)
  have h_expand : (|t| + 2)^3 = (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    ring
  have h3 : |t| + 3 ≤ (|t| + 2)^3 := by
    simpa [h_expand] using h_add
                           
  exact le_trans (le_trans h1a h17le3) h3

lemma lem_DlogImlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    Real.log (|z.im| + 2) ≤ 3 * Real.log (|t| + 2) := by
  intro t ht z hz
                                                                           
  have h1 : |z.im| + 2 ≤ (|t| + 2)^3 := lem_DIMt2 t ht z hz
                                           
  have h2 : 0 < |z.im| + 2 := by
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
                        
  have hlog := Real.log_le_log h2 h1
                                  
  simpa [Real.log_pow] using hlog

lemma lem_D1logtlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    (1 : ℝ) / Real.log (|t| + 2) ≤ 3 / Real.log (|z.im| + 2) := by
  intro t ht z hz
  have h1 := lem_DlogImlog t ht z hz
                                                     
  have ht_pos : |t| + 2 > 1 := by linarith [abs_nonneg t]
  have hz_pos : |z.im| + 2 > 1 := by linarith [abs_nonneg z.im]
  have log_t_pos : Real.log (|t| + 2) > 0 := Real.log_pos ht_pos
  have log_z_pos : Real.log (|z.im| + 2) > 0 := Real.log_pos hz_pos

  rw [div_le_div_iff₀ log_t_pos log_z_pos]
  simp only [one_mul]
  exact h1

lemma lem_Ddt2dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    deltaz_t t ≤ 3 * deltaz z := by
  intro t ht z hz
  have h := lem_D1logtlog t ht z hz
  have hpos : 0 ≤ zerofree_constant / 20 := by
    have ha : 0 < zerofree_constant := zerofree_constant_pos
    have h9 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt ha) (le_of_lt h9)
  have h2 := mul_le_mul_of_nonneg_left h hpos
  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
            simp [deltaz_t, deltaz]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (3 / Real.log (|z.im| + 2)) := h2
    _ = 3 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
            simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
    _ = 3 * deltaz z := by simp [deltaz, div_eq_mul_inv, mul_left_comm, mul_assoc]

lemma lem_deltarhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → deltaz ρ ≥ (1/3) * deltaz_t t := by
  intro c hρK
  rcases hρK with ⟨hball, _hzero⟩
  have hball' : ρ ∈ Metric.closedBall ((3/2 : ℂ) + t * Complex.I) (5/6) := by
    simpa [c, mul_comm] using! hball
  have hmain : deltaz_t t ≤ 3 * deltaz ρ := lem_Ddt2dz t ht ρ hball'
  have hthird_nonneg : 0 ≤ (1/3 : ℝ) := by norm_num
  have h_mul : (1/3 : ℝ) * deltaz_t t ≤ (1/3 : ℝ) * (3 * deltaz ρ) :=
    mul_le_mul_of_nonneg_left hmain hthird_nonneg
  have h_simplify : (1/3 : ℝ) * (3 * deltaz ρ) = deltaz ρ := by
    ring
  have : (1/3 : ℝ) * deltaz_t t ≤ deltaz ρ := by
    simpa [h_simplify] using h_mul
  simpa [mul_comm] using this

lemma lem_Rerhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → ρ.re ≤ 1 - 3 * deltaz_t t := by
  intros c h_rho_in
                                                          
  have h1 : ρ.re ≤ 1 - 9 * deltaz ρ :=
    lem_Rerhotodeltarho (ρ := ρ) t ht (by simpa [c, mul_comm] using! h_rho_in)
                                                         
  have h2 : deltaz ρ ≥ (1/3) * deltaz_t t := lem_deltarhotodeltat t ht ρ h_rho_in
                                                         
  have h3 : 9 * deltaz ρ ≥ 3 * deltaz_t t := by
    calc
      9 * deltaz ρ
          ≥ 9 * ((1/3) * deltaz_t t) := by
                exact mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 9)
      _ = 9 * (1/3) * deltaz_t t := by ring
      _ = 3 * deltaz_t t := by norm_num
                                         
  have h4 : 1 - 9 * deltaz ρ ≤ 1 - 3 * deltaz_t t := by
    linarith [h3]
                                                        
  exact le_trans h1 h4

lemma lem_RezRerho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    z.re - ρ.re ≥ 2 * deltaz_t t := by
  intro c h_rho_mem h_z
                                                     
  have h_rho_bound := lem_Rerhotodeltat t ht ρ h_rho_mem
                                                
  have h_z_lower := h_z.1
                                                                                      
  linarith [h_z_lower, h_rho_bound]

lemma lem_abszrhodelta (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖z - ρ‖ ≥ 2 * deltaz_t t := by
  intro c h_rho_in_K h_z_conditions
                                                         
  have h1 : z.re - ρ.re ≥ 2 * deltaz_t t := (lem_RezRerho t ht z ρ) h_rho_in_K h_z_conditions
                                                     
  have h2 : ‖z - ρ‖ ≥ z.re - ρ.re := lem_abszrhoReRe z ρ
                                                                    
  exact le_trans h1 h2

lemma lem_abszrhodeltanot0 (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖z - ρ‖ > 0 := by
  intro c hmem hbounds
                                                           
  have h1 := lem_abszrhodelta t ht z ρ hmem hbounds
                                            
  have h2 := lem_delta19.2 t (by linarith [ht] : |t| > 2)
  have h3 : 0 < deltaz_t t := h2.1
                                                     
  have h4 : 0 < 2 * deltaz_t t := by
    linarith [h3]
                                                                 
  linarith [h1, h4]

lemma lem_1abszrho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) := by
  intro c hρ hz
                                                              
  apply one_div_le_one_div_of_le
                                           
  · have h_delta_pos : 0 < deltaz_t t := by
      have h_delta19 := lem_delta19
      exact (h_delta19.2 t (by linarith [ht] : |t| > 2)).1
    linarith [h_delta_pos]
                                                  
  · exact lem_abszrhodelta t ht z ρ hρ hz

lemma lem_m_rho_zeta_nat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → ∃ n : ℕ, (analyticOrderAt riemannZeta ρ) = n := by
  intro c hρK
  classical
                                
  have ht1 : |t| > 1 := lt_trans (by norm_num) ht
                                              
  have hρ_in_ball1 : ρ ∈ Metric.closedBall c 1 := by
    have hρ_le : dist ρ c ≤ (5 / 6 : ℝ) := by simpa [Metric.mem_closedBall] using hρK.1
    have : dist ρ c ≤ (1 : ℝ) := le_trans hρ_le (by norm_num)
    simpa [Metric.mem_closedBall] using this
                
  have hρ_ne_one : ρ ≠ (1 : ℂ) := (D1cinTt_pre t ht1) ρ hρ_in_ball1
                                     
  have hζ_analytic_at_ρ : AnalyticAt ℂ riemannZeta ρ := zetaanalOnnot1 ρ hρ_ne_one
                                                                                                    
  have h_not_eventually_zero : ¬ (∀ᶠ z in nhds ρ, riemannZeta z = 0) := by
    by_contra h_ev
                                                
    have h_freq := eventually_eq_zero_implies_frequently_eq_zero_punctured riemannZeta ρ h_ev
                                                                         
    have h_zero_on_S :=
      zetaanalOnnot1.eqOn_zero_of_preconnected_of_frequently_eq_zero
        complex_minus_singleton_connected hρ_ne_one h_freq
                                     
    have hc_in_ball1 : c ∈ Metric.closedBall c 1 := by
      have : dist c c ≤ (1 : ℝ) := by simp [dist_self]
      simp [Metric.mem_closedBall]
    have hc_ne_one : c ≠ (1 : ℂ) := (D1cinTt_pre t ht1) c hc_in_ball1
    have hc_in_S : c ∈ {s : ℂ | s ≠ 1} := by simpa [Set.mem_ofPred_eq] using hc_ne_one
    have hζc_zero : riemannZeta c = 0 := h_zero_on_S hc_in_S
    exact (zetacnot0 t) hζc_zero
                                            
  have hfinite : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    have hiff : analyticOrderAt riemannZeta ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, riemannZeta z = 0 :=
      analyticOrderAt_eq_top (f := riemannZeta) (z₀ := ρ)
    have : ∀ᶠ z in nhds ρ, riemannZeta z = 0 := hiff.mp htop
    exact h_not_eventually_zero this
                                                                       
  refine ⟨(analyticOrderAt riemannZeta ρ).toNat, ?_⟩
  simpa using (ENat.natCast_toNat hfinite).symm

lemma lem_finiteKzeta (t : ℝ) (_ht : |t| > 3) :
    let c := (3/2 : ℂ) + I * t
    (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite := by
  intro c
  have hK : IsCompact (Metric.closedBall c (5 / (6 : ℝ))) :=
    closedBall_compact_complex c (5 / (6 : ℝ))
  simpa [zerosetKfRc] using
    (riemannZeta_zeros_finite_of_compact (Metric.closedBall c (5 / (6 : ℝ))) hK)

lemma lem_triangle_ZFR (t : ℝ) (_ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) := by
                                                                                                  
  intros c hfin hz_cond

  apply le_trans (norm_sum_le _ _)

  apply Finset.sum_le_sum
  intro ρ hρ

  rw [norm_div]

  rw [Complex.norm_natCast]

lemma lem_Zeta_Triangle_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
        ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ +
        C_1 * Real.log |t| := by
  obtain ⟨C1, hC1, hbound⟩ := lem_Zeta_Expansion_ZFR
  refine ⟨C1, hC1, ?_⟩
  intro t ht c hfin z hz
                                           
  let S := (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))
  have hbound1 := hbound t ht hfin z hz
  have htri : ‖deriv riemannZeta z / riemannZeta z‖ ≤ ‖(deriv riemannZeta z / riemannZeta z) - S‖ + ‖S‖ := by
    have hn := norm_add_le ((deriv riemannZeta z / riemannZeta z) - S) S
    have hrewrite : (deriv riemannZeta z / riemannZeta z) - S + S = (deriv riemannZeta z / riemannZeta z) := by
      simp [sub_eq_add_neg]
    simpa [S, hrewrite] using hn
  have hsum := add_le_add_left hbound1 ‖S‖
  have : ‖deriv riemannZeta z / riemannZeta z‖ ≤ C1 * Real.log |t| + ‖S‖ := le_trans htri hsum
  simpa [S, add_comm] using this

lemma lem_sumK1abs (t : ℝ) (ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
    (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := by
  intro c hfin hzcond
                                       
  have hptwise : ∀ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖ ≤
      (1 / (2 * deltaz_t t)) * ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    intro ρ hρmem
    have hρ_in : ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρmem
    have hbase : 1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) :=
      lem_1abszrho t ht z ρ hρ_in hzcond
    have hnonneg : 0 ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le ((analyticOrderAt riemannZeta ρ).toNat))
    have := mul_le_mul_of_nonneg_left hbase hnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum := Finset.sum_le_sum hptwise
                                                                
  have hrw :=
    (Finset.mul_sum (s := hfin.toFinset)
      (f := fun ρ => ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
      (a := (1 / (2 * deltaz_t t))))
  have hsum2 := hsum
                                                        
  rw [← hrw] at hsum2
           
  simpa [div_eq_mul_inv] using hsum2

lemma helper_analyticOnNhd_shift_div (f : ℂ → ℂ) (c : ℂ)
    (h : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
    (_hc : f c ≠ 0) :
    AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (Metric.closedBall (0 : ℂ) 1) := by
                                                                                     
  intro z hz
                                                 
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
                                                                   
  have hz_addc_mem : z + c ∈ Metric.closedBall c 1 := by
                                           
    have : dist (z + c) c ≤ 1 := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz_norm
    simpa [Metric.mem_closedBall] using this
                                               
  have h_f_at : AnalyticAt ℂ f (z + c) := h (z + c) hz_addc_mem
                                               
  have h_addc : AnalyticAt ℂ (fun w => w + c) z := by
    simpa using! (analyticAt_id.add analyticAt_const)
                                                              
  have h_comp : AnalyticAt ℂ (fun w => f (w + c)) z :=
    (AnalyticAt.fun_comp h_f_at h_addc)
                                                                                            
  have h_mul_const : AnalyticAt ℂ (fun w => (1 / f c) * f (w + c)) z :=
    (analyticAt_const.mul h_comp)
                                
  simpa [div_eq_mul_inv, mul_comm] using h_mul_const

lemma helper_finite_zeros_shift (r : ℝ) (_hr : r > 0) (c : ℂ) (f : ℂ → ℂ)
    (hc : f c ≠ 0)
    (_h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
    (hfin : (zerosetKfRc r c f).Finite) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  let g : ℂ → ℂ := fun z => f (z + c) / f c
  have hEq :
      zerosetKfRc r (0 : ℂ) g = (fun ρ : ℂ => ρ - c) '' zerosetKfRc r c f := by
    apply Set.Subset.antisymm
    · intro x hx
                                       
      have hx_ball : dist x (0 : ℂ) ≤ r := by
        simpa [Metric.mem_closedBall] using hx.1
                                     
      have hx_ball' : dist (x + c) c ≤ r := by
        simpa [Complex.dist_eq, add_sub_cancel] using hx_ball
                                              
      have hx_zero : f (x + c) = 0 := by
        rcases (div_eq_zero_iff).mp (by simpa [g] using hx.2) with hnum | hden
        · exact hnum
        · exact (hc hden).elim
      refine ⟨x + c, ?_, ?_⟩
      · exact ⟨by simpa [Metric.mem_closedBall] using hx_ball', hx_zero⟩
      · simp
    · intro x hx
      rcases hx with ⟨ρ, hρ, rfl⟩
                                       
      have hρ_ball : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ.1
      refine ⟨?_, ?_⟩
      ·                                
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hρ_ball
      ·                 
        have : f ρ = 0 := hρ.2
        simp [g, sub_add_cancel, this]
                                                                 
  have himage : ((fun ρ : ℂ => ρ - c) '' zerosetKfRc r c f).Finite :=
    hfin.image (fun ρ : ℂ => ρ - c)
  simpa [g, hEq] using himage

lemma helper_bound_shifted (B R : ℝ) (_hB : 1 < B) (_hRpos : 0 < R) (_hRlt1 : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
    (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ :=
by
  intro z hz
                                            
  have hz_norm : ‖z‖ ≤ R := by
    have hz' : dist z (0 : ℂ) ≤ R := by simpa [Metric.mem_closedBall] using hz
    simpa [Complex.dist_eq] using hz'
                                 
  have hz_ballc : z + c ∈ Metric.closedBall c R := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel] using hz_norm
                                                  
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_ballc
                                        
  have hpos : 0 < ‖f c‖ := (norm_pos_iff).2 hc
                                   
  have hdiv : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ := (div_le_div_iff_of_pos_right hpos).2 hfb
                                              
  have hnorm_eq : ‖(fun w => f (w + c) / f c) z‖ = ‖f (z + c)‖ / ‖f c‖ := by
    change ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖
    simp
  simpa [hnorm_eq] using hdiv

lemma helper_g_zero_eq_one (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0) :
  (fun z => f (z + c) / f c) 0 = 1 := by
  simp [hc]

lemma helper_zerosetKfR_eq_center0 (r : ℝ) (hr : r > 0) (f : ℂ → ℂ) :
  zerosetKfR r hr f = zerosetKfRc r (0 : ℂ) f := by
  ext ρ; simp [zerosetKfR, zerosetKfRc]

lemma helper_sum_nonneg_nat (ι : Type*) (s : Finset ι) (f : ι → ℕ) :
  0 ≤ ∑ i ∈ s, ((f i : ℝ)) := by
  classical
  have h : ∀ i ∈ s, (0 : ℝ) ≤ (f i : ℝ) := by
    intro i hi
    exact_mod_cast (Nat.zero_le (f i))
  simpa using Finset.sum_nonneg h

lemma helper_one_le_Bdivfc2 (B R : ℝ) (_hB : 1 < B) (hRpos : 0 < R) (_hRlt1 : R < 1)
  (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0)
  (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
  1 ≤ B / ‖f c‖ :=
by
  have hc_in : c ∈ Metric.closedBall c R := by
    have h0le : (0 : ℝ) ≤ R := le_of_lt hRpos
    simpa [Metric.mem_closedBall, dist_self] using h0le
  have hfc_le : ‖f c‖ ≤ B := h_bound c hc_in
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff.mpr hc)
  have hdiv := (div_le_div_iff_of_pos_right (c := ‖f c‖) hfc_pos).mpr hfc_le
  simpa [div_self (ne_of_gt hfc_pos)] using hdiv

lemma helper_sum_over_equal_finite_sets {α : Type*} (S T : Set α)
  (hS : S.Finite) (hT : T.Finite) (hST : S = T) (φ : α → ℝ) :
  (∑ x ∈ hS.toFinset, φ x) = (∑ x ∈ hT.toFinset, φ x) := by
  classical
  have hfin_eq : hS.toFinset = hT.toFinset := by
    ext x
    constructor
    · intro hx
      have hxS : x ∈ S := by
        have hmem : x ∈ hS.toFinset ↔ x ∈ S := by
          simp
        exact hmem.mp hx
      have hxT : x ∈ T := by simpa [hST] using hxS
      have hmemT : x ∈ hT.toFinset ↔ x ∈ T := by
        simp
      exact hmemT.mpr hxT
    · intro hx
      have hxT : x ∈ T := by
        have hmemT : x ∈ hT.toFinset ↔ x ∈ T := by
          simp
        exact hmemT.mp hx
      have hxS : x ∈ S := by simpa [hST] using hxT
      have hmemS : x ∈ hS.toFinset ↔ x ∈ S := by
        simp
      exact hmemS.mpr hxS
  simp [hfin_eq]

lemma helper_apply_jensen_to_g
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤ Real.log B / Real.log (R / R1) := by
  classical
                                                     
  have h_exists : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      ∃ hσ : ℂ → ℂ, AnalyticAt ℂ hσ σ ∧ hσ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * hσ z := by
    intro σ hσ
    exact lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 g h_g_analytic hg0_ne σ hσ
                                            
  let h_σ : ℂ → (ℂ → ℂ) :=
    fun σ => dite (σ ∈ zerosetKfR R1 (by linarith) g)
      (fun h => Classical.choose (h_exists σ h))
      (fun _ => fun _ => (1 : ℂ))
                                             
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      AnalyticAt ℂ (h_σ σ) σ ∧ (h_σ σ) σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * (h_σ σ) z := by
    intro σ hσin
    have hx := h_exists σ hσin
    dsimp [h_σ]
                                  
    simpa [hσin] using (Classical.choose_spec hx)
                                      
  have hbound :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1
      g h_g_analytic hg0_ne hg0_one hfin_g (h_σ := h_σ) hg_le_B h_σ_spec
                                         
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound

lemma helper_sum_f_equals_sum_g
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
  =
  (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
      ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) :=
by
  classical
             
  let S : Finset ℂ := hfin.toFinset
  let φ : ℂ → ℂ := fun ρ => ρ - c
  let g' : ℂ → ℂ := fun z => f (z + c) / f c

  have himg : (φ '' zerosetKfRc r c f).Finite := hfin.image φ
  have h_img_toFinset : ((hfin.image φ).toFinset) = S.image φ := by
    simpa [S] using (Set.Finite.toFinset_image (s := (zerosetKfRc r c f)) (f := φ)
      (hs := hfin) (h := himg))

  have h_orders_match :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρS
                                                                          
    have hρ_mem : ρ ∈ zerosetKfRc r c f :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρS
    have hρ_ball : ρ ∈ Metric.closedBall c r := hρ_mem.1
    have hρ_fzero : f ρ = 0 := hρ_mem.2
                                                                   
    have hρ'_ball : (φ ρ) ∈ Metric.closedBall (0 : ℂ) r := by
                     
      have hdist_le : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ_ball
                                               
      have : dist (φ ρ) 0 ≤ r := by
        simpa [φ, dist_eq_norm] using (by simpa [dist_eq_norm] using hdist_le)
      simpa [Metric.mem_closedBall] using this
    have hρ'_gzero : g' (φ ρ) = 0 := by
      simp [g', φ, hρ_fzero, sub_eq_add_neg, add_comm]
    have hρ'_mem : (φ ρ) ∈ zerosetKfRc r (0 : ℂ) g' := ⟨hρ'_ball, hρ'_gzero⟩
                                                
    have h_m_eq := fc_m_order r hr c f hc h_analytic (ρ' := φ ρ) hρ'_mem
                    
    have h_m_eq' : analyticOrderAt g' (φ ρ) = analyticOrderAt f ρ := by
      simpa [g', φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_m_eq
                                  
    have h_toNat : (analyticOrderAt g' (φ ρ)).toNat = (analyticOrderAt f ρ).toNat := by
      simpa using congrArg ENat.toNat h_m_eq'
    simp [h_toNat]

  have h_inj : Function.Injective φ := by
    intro x y hxy
                                                    
    have := congrArg (fun z => z + c) hxy
    simpa [φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  have h_sum_image :
      (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    refine Finset.sum_image ?h
    intro x hx y hy hxy
                                
    exact h_inj hxy

  calc
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) := by rfl
    _ = (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := h_orders_match
    _ = (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) := h_sum_image.symm
    _ = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) := by
                                                     
          simp [S, φ, g', h_img_toFinset]

lemma helper_zero_set_shift_eq
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1)) :
  zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
  = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  simpa using fc_zeros r hr c f hc h_analytic

lemma helper_fin_zero_g_is_image
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  have hset : zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
      = (fun ρ => ρ - c) '' (zerosetKfRc r c f) :=
    by simpa using fc_zeros r hr c f hc h_analytic
  have hfin_img : ((fun ρ => ρ - c) '' (zerosetKfRc r c f)).Finite := hfin.image _
  simpa [hset] using hfin_img

lemma helper_AnalyticOnNhd_to_pointwise {S : Set ℂ} {f : ℂ → ℂ}
  (h : AnalyticOnNhd ℂ f S) : ∀ z ∈ S, AnalyticAt ℂ f z := by
  intro z hz
  exact h z hz

lemma jensen_sum_bound_strict
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤
    Real.log B / Real.log (R / R1) := by
  exact helper_apply_jensen_to_g B R R1 hB hR1_pos hR1_lt_R hR_lt_1 g
    h_g_analytic hg0_ne hg0_one hfin_g hg_le_B

lemma no_zero_of_bound_one_and_center_one
  (R : ℝ) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_one : g 0 = 1)
  (hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1) :
  ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
  intro z hz
  by_cases hRpos : 0 < R
  ·
                                             
    have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
      intro x hx
      have hxlt : ‖x‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans (le_of_lt hxlt) (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact ((h_g_analytic x hx_in1).differentiableAt).differentiableWithinAt
                                                
    have hcont : ContinuousOn g (Metric.closedBall (0 : ℂ) R) := by
      intro x hx
      have hxleR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans hxleR (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact (h_g_analytic x hx_in1).continuousAt.continuousWithinAt
    have hdcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) :=
      DiffContOnCl.mk_ball hdiff hcont
                                                               
    have hIsMax : IsMaxOn (fun z => ‖g z‖) (Metric.ball (0 : ℂ) R) 0 := by
      intro y hy
      have hynormlt : ‖y‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hy
      have hyle : ‖y‖ ≤ R := le_of_lt hynormlt
      have hgy : ‖g y‖ ≤ 1 := hg_le_one y hyle
      simpa [hg0_one] using hgy
                                                         
    have hEqOn :=
      Complex.eqOn_closedBall_of_isMaxOn_norm (z := (0 : ℂ)) (r := R) hdcc hIsMax
    have hz_eq : g z = (fun _ => g 0) z := hEqOn hz
    have hz_eq1 : g z = g 0 := by simpa using hz_eq
    have gz_one : g z = 1 := by simpa [hg0_one] using hz_eq1
    simp [gz_one]
  ·
                                                                           
    have hRle : R ≤ 0 := le_of_not_gt hRpos
    have hz_le : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
    have hz_norm_eq : ‖z‖ = 0 :=
      le_antisymm (le_trans hz_le hRle) (norm_nonneg z)
    have hz_zero : z = 0 := by
      simpa [norm_eq_zero] using hz_norm_eq
    simp [hz_zero, hg0_one]

lemma helper_sum_over_equal_finite_sets_orders
  {S T : Set ℂ} (g : ℂ → ℂ)
  (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
  (∑ x ∈ hS.toFinset, ((analyticOrderAt g x).toNat : ℝ))
  = (∑ x ∈ hT.toFinset, ((analyticOrderAt g x).toNat : ℝ)) := by
  classical
  have hF : hS.toFinset = hT.toFinset := by
    ext x
    simp [Set.Finite.mem_toFinset, hST]
  simp [hF]

lemma helper_mem_closedBall_zero_iff_norm_le (z : ℂ) (R : ℝ) :
  z ∈ Metric.closedBall (0 : ℂ) R ↔ ‖z‖ ≤ R := by
  simp [Metric.mem_closedBall, dist_eq_norm]

lemma helper_bound_on_ball_to_norm_imp
  {R : ℝ} {g : ℂ → ℂ} {M : ℝ}
  (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ M) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M := by
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R := by
    have : dist z (0 : ℂ) ≤ R := by
      simpa [dist_eq_norm] using hz
    simpa [Metric.mem_closedBall] using this
  exact hg z hz'

lemma helper_pointwise_to_AnalyticOnNhd {S : Set ℂ} {f : ℂ → ℂ}
  (h : ∀ z ∈ S, AnalyticAt ℂ f z) : AnalyticOnNhd ℂ f S := by
  simpa using! h

lemma lem_sum_m_rho_bound_c (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (hR_lt_1 : R < 1)
  (f : ℂ → ℂ)
  (c : ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
  (h_f_nonzero_at_zero : f c ≠ 0)
  (hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B)
  (hfin : (zerosetKfRc R1 c f).Finite) :
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
  classical
                                                   
  let g : ℂ → ℂ := fun z => f (z + c) / f c

  have h_g_analyticOn : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    helper_analyticOnNhd_shift_div f c h_f_analytic h_f_nonzero_at_zero
  have h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z :=
    helper_AnalyticOnNhd_to_pointwise h_g_analyticOn

  have hg0_one : g 0 = 1 := helper_g_zero_eq_one f c h_f_nonzero_at_zero
  have hg0_ne : g 0 ≠ 0 := by simp [hg0_one]

  have hAnal_f : AnalyticOnNhd ℂ f (Metric.closedBall c 1) :=
    helper_pointwise_to_AnalyticOnNhd h_f_analytic
  have hfin_g0 : (zerosetKfRc R1 (0 : ℂ) g).Finite :=
    helper_fin_zero_g_is_image R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f hfin
  have hZR_eq : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
    helper_zerosetKfR_eq_center0 R1 hR1_pos g
  have hfin_g : (zerosetKfR R1 (by exact hR1_pos) g).Finite := by
    simpa [hZR_eq] using hfin_g0

  have h_bound_shift : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_shifted B R hB (by exact lt_trans hR1_pos hR1_lt_R) hR_lt_1 c f
      h_f_nonzero_at_zero (fun z hz => hf_le_B z <| by simpa using hz)
  have hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_on_ball_to_norm_imp (R := R) (g := g) (M := B / ‖f c‖) h_bound_shift

  have hfc_le : ‖f c‖ ≤ B := by
    have : c ∈ Metric.closedBall c R := by
      have hRpos' : 0 ≤ R := le_of_lt (lt_trans hR1_pos hR1_lt_R)
      have : dist c c ≤ R := by simpa [dist_self] using hRpos'
      simpa [Metric.mem_closedBall] using this
    exact hf_le_B c this
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff).2 h_f_nonzero_at_zero
  have hBdiv_ge_one : 1 ≤ B / ‖f c‖ := by
    have hdiv := (div_le_div_iff_of_pos_right hfc_pos).mpr hfc_le
    simpa [div_self (ne_of_gt hfc_pos)] using hdiv

  have hsum_fg_eq :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt g ρ').toNat : ℝ)) :=
    helper_sum_f_equals_sum_g (r := R1) (hr := hR1_pos) (c := c)
      (f := f) (hc := h_f_nonzero_at_zero) (h_analytic := hAnal_f) (hfin := hfin)

  have hST_g_img : zerosetKfR R1 hR1_pos g
      = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) := by
    have h1 : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
      helper_zerosetKfR_eq_center0 R1 hR1_pos g
    have h2 : zerosetKfRc R1 (0 : ℂ) g
        = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
      helper_zero_set_shift_eq R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f
    simpa [h1] using h2

  rcases lt_or_eq_of_le hBdiv_ge_one with hBdiv_gt_one | hBdiv_eq_one
  ·                                                            
    have hsum_g_bound :=
      jensen_sum_bound_strict (B := B / ‖f c‖) (R := R) (R1 := R1)
        (hB := hBdiv_gt_one)
        (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
        (g := g) (h_g_analytic := h_g_analytic) (hg0_ne := hg0_ne)
        (hg0_one := hg0_one) (hfin_g := hfin_g) (hg_le_B := hg_le_B)
                                                                           
    have hsum_g_reindex :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
                                                                     
    have :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simpa [hsum_g_reindex] using hsum_g_bound
                                              
    simpa [hsum_fg_eq] using this
  ·                                                                                    
    have hBdiv_eq_one' : B / ‖f c‖ = 1 := by
      simpa [eq_comm] using hBdiv_eq_one
    have hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1 := by
      intro z hz
      have := hg_le_B z hz
      simpa [hBdiv_eq_one'] using this
    have g_nonzero_on_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 :=
      no_zero_of_bound_one_and_center_one R hR_lt_1 g h_g_analytic hg0_one hg_le_one
                                                                      
    have hS_empty : zerosetKfR R1 hR1_pos g = (∅ : Set ℂ) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzball, hzzero⟩
        have hzR1 : ‖z‖ ≤ R1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
        have hzR : ‖z‖ ≤ R := le_trans hzR1 (le_of_lt hR1_lt_R)
        have hzR' : z ∈ Metric.closedBall (0 : ℂ) R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
        exact (g_nonzero_on_ball z hzR') hzzero
      · intro hzfalse
        cases hzfalse
    have hsum_g_zero :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      have h :=
        helper_sum_over_equal_finite_sets_orders (g := g)
          (S := zerosetKfR R1 hR1_pos g) (T := (∅ : Set ℂ))
          (hS := hfin_g) (hT := Set.finite_empty) (hST := hS_empty)
      simpa using h
                                                                                         
    have hsum_reindex :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    have hsum_img_eq :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) := by
      simpa using hsum_reindex.symm
    have hsum_img_zero :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      simp [hsum_img_eq, hsum_g_zero]
                                                  
    have hsum_f_zero :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) = 0 := by
      simpa [hsum_img_zero] using hsum_fg_eq
                                                   
    have hRHS_zero : Real.log (B / ‖f c‖) / Real.log (R / R1) = 0 := by
      simp [hBdiv_eq_one']
                                      
    have :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simp [hsum_f_zero, hRHS_zero]
    exact this

lemma lem_sum_m_rho_zeta :
    ∃ C_2 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ C_2 * Real.log |t| := by
  classical
                                    
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨a, ha_pos, ha_bound⟩ := zeta_low_332
          
  let R1 : ℝ := 5 / 6
  let R : ℝ := 8 / 9
  let logRatio : ℝ := Real.log (R / R1)
                                 
  let u : ℝ := Real.log (b / a)
  let C2 : ℝ := max 2 ((1 + |u|) / logRatio)
  have hC2_gt_one : 1 < C2 := by
    have htwo_lt : (1 : ℝ) < 2 := by norm_num
    have hle : (2 : ℝ) ≤ C2 := by
      have := le_max_left (2 : ℝ) ((1 + |u|) / logRatio)
      simp [C2]
    exact lt_of_lt_of_le htwo_lt hle
  refine ⟨C2, hC2_gt_one, ?_⟩
  intro t ht c hfin
                              
  have hR1_pos : 0 < R1 := by dsimp [R1]; norm_num
  have hR1_lt_R : R1 < R := by dsimp [R1, R]; norm_num
  have hR_lt_1 : R < 1 := by dsimp [R]; norm_num
  have hR_le_one : R ≤ (1 : ℝ) := by dsimp [R]; norm_num
                                                                                          
  have ht1 : |t| > 1 := lt_trans (by norm_num) ht
  have h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ riemannZeta z := by
    intro z hz
    have hz_ne_one : z ≠ (1 : ℂ) := (D1cinTt_pre t ht1) z (by simpa [c] using hz)
    exact zetaanalOnnot1 z hz_ne_one
                      
  have h_nonzero : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
                                                          
  have ht2 : |t| > 2 := by linarith
  have h_upper_on_ball1 : ∀ z ∈ Metric.closedBall c 1, ‖riemannZeta z‖ < b * |t| := by
    have h := hb_bound t ht2
    intro z hz; simpa [c] using h z (by simpa [c] using hz)
  have hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖riemannZeta z‖ ≤ b * |t| := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall c 1 :=
      (Metric.closedBall_subset_closedBall hR_le_one) hz
    exact le_of_lt (h_upper_on_ball1 z hz1)
                         
  have hb_pos : 0 < b := lt_trans (by norm_num) hb_gt1
  have htabove1 : (1 : ℝ) ≤ |t| := le_of_lt ht1
  have hb_le_B : b ≤ b * |t| := by
    have := mul_le_mul_of_nonneg_left htabove1 (le_of_lt hb_pos)
    simpa [one_mul] using this
  have hBpos : 1 < b * |t| := lt_of_lt_of_le hb_gt1 hb_le_B
                                                                  
  have h_sum_bound :=
    lem_sum_m_rho_bound_c (B := b * |t|) (R := R) (R1 := R1)
      (hB := hBpos)
      (hR1_pos := hR1_pos)
      (hR1_lt_R := hR1_lt_R)
      (hR_lt_1 := hR_lt_1)
      (f := riemannZeta) (c := c)
      (h_f_analytic := h_f_analytic)
      (h_f_nonzero_at_zero := h_nonzero)
      (hf_le_B := hf_le_B)
      (hfin := hfin)
                           
  have hlogRatio_pos : 0 < logRatio := by
    have : 1 < R / R1 := by dsimp [R, R1]; norm_num
    exact Real.log_pos this
                          
  have h_zeta_ge_a : a ≤ ‖riemannZeta c‖ := by
    simpa [c, mul_comm] using! ha_bound t

  have ht_abs_pos : 0 < |t| := lt_trans (by norm_num) ht
  have hζ_norm_pos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr h_nonzero
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have ht_abs_ne : (|t| : ℝ) ≠ 0 := ne_of_gt ht_abs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_split1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        = (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖ := by
    have : Real.log (b * |t|) = Real.log b + Real.log |t| :=
      Real.log_mul hb_ne ht_abs_ne
    have :
        Real.log ((b * |t|) / ‖riemannZeta c‖)
          = Real.log (b * |t|) - Real.log ‖riemannZeta c‖ :=
      Real.log_div (by exact mul_ne_zero hb_ne ht_abs_ne) (ne_of_gt hζ_norm_pos)
    simp [this, Real.log_mul hb_ne ht_abs_ne]
  have hlog_div_eq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb_ne ha_ne
  have hlog_a_le : Real.log a ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log (by exact ha_pos) (by exact h_zeta_ge_a)
  have hneg : -(Real.log ‖riemannZeta c‖) ≤ -Real.log a := by
    simpa using (neg_le_neg hlog_a_le)
  have hRHS_le_const :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        ≤ Real.log |t| + Real.log (b / a) := by
                                       
    have :
        (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖
          ≤ (Real.log b + Real.log |t|) - Real.log a := by
      simpa [sub_eq_add_neg] using! add_le_add_right hneg (Real.log b + Real.log |t|)
    simpa [hlog_split1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlog_div_eq]
      using this
                                
  have hRHS1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖) / logRatio
        ≤ (Real.log |t| + Real.log (b / a)) / logRatio := by
    exact div_le_div_of_nonneg_right hRHS_le_const (le_of_lt hlogRatio_pos)
                                   
  have hlogt_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                          
    have h3le : (3 : ℝ) ≤ |t| := le_of_lt ht
    have hlog3_le : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) h3le
    have h_exp_le : Real.exp (1 : ℝ) ≤ 3 := le_of_lt lem_three_gt_e
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).mpr h_exp_le
    exact le_trans hlog3_ge_one hlog3_le
  have hadd_le : Real.log |t| + Real.log (b / a) ≤ (1 + |u|) * Real.log |t| := by
    have haux1 : Real.log (b / a) ≤ |u| := by simpa [u] using le_abs_self (Real.log (b / a))
    have haux2 : |u| ≤ |u| * Real.log |t| := by
      have hnonneg : 0 ≤ |u| := abs_nonneg _
      have h1le : (1 : ℝ) ≤ Real.log |t| := hlogt_ge_one
      simpa [one_mul] using (mul_le_mul_of_nonneg_left h1le hnonneg)
    calc
      Real.log |t| + Real.log (b / a)
          ≤ Real.log |t| + |u| := by exact add_le_add_right haux1 _
      _ ≤ Real.log |t| + (|u| * Real.log |t|) := by exact add_le_add_right haux2 _
      _ = (1 + |u|) * Real.log |t| := by ring
  have hRHS2 :
      (Real.log |t| + Real.log (b / a)) / logRatio
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := div_le_div_of_nonneg_right hadd_le (le_of_lt hlogRatio_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hfinal :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := le_trans h_sum_bound hRHS1
    exact le_trans this hRHS2
                              
  have hC2_ge : ((1 + |u|) / logRatio) ≤ C2 := by
    have := le_max_right (2 : ℝ) ((1 + |u|) / logRatio)
    simp [C2]
  have hlogt_nonneg : 0 ≤ Real.log |t| := le_trans (by norm_num) hlogt_ge_one
  have hscale := mul_le_mul_of_nonneg_right hC2_ge hlogt_nonneg
  exact le_trans hfinal hscale

lemma lem_sumKdeltatlogt :
  ∃ C_3 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t;
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      (C_3 / (deltaz_t t)) * Real.log |t| := by
                                        
  obtain ⟨C_2, hC_2_pos, hC_2_bound⟩ := lem_sum_m_rho_zeta

  use C_2

  constructor
  ·                                             
    exact hC_2_pos

  ·              
    intro t ht c hfin z hz

    have h1 := lem_sumK1abs t ht z hfin hz

    have h2 := hC_2_bound t ht hfin

    have ht2 : |t| > 2 := by linarith [ht]
    have h_delta_pos : 0 < deltaz_t t := (lem_delta19.2 t ht2).1

    have h_t_ge_one : (1 : ℝ) ≤ |t| := by linarith [ht]

    calc
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := h1
      _ ≤ (1 / (2 * deltaz_t t)) * (C_2 * Real.log |t|) := by
          apply mul_le_mul_of_nonneg_left h2
          apply div_nonneg (by norm_num)
          apply mul_nonneg (by norm_num) (le_of_lt h_delta_pos)
      _ = (C_2 / (2 * deltaz_t t)) * Real.log |t| := by ring
      _ ≤ (C_2 / deltaz_t t) * Real.log |t| := by
          apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg h_t_ge_one)
                                                           
          apply div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hC_2_pos))
          · exact h_delta_pos
          ·                                    
            calc deltaz_t t
              = 1 * deltaz_t t := by rw [one_mul]
            _ ≤ 2 * deltaz_t t := by
              apply mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt h_delta_pos)

lemma lem_sumKlogt2 :
  ∃ C_4 > 1, ∀ (t : ℝ) (_ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      C_4 * Real.log |t|^2 := by
                                        
  obtain ⟨C_3, hC_3_gt, hC_3⟩ := lem_sumKdeltatlogt

  use max (100 * C_3 / zerofree_constant) 2

  constructor
  · exact lt_max_of_lt_right (by norm_num : (2 : ℝ) > 1)

  · intro t ht c hfin z hz
                                              
    have h_bound := hC_3 t ht hfin z hz

    have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
    have h_log_t_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
    have hC_3_pos : 0 < C_3 := lt_trans zero_lt_one hC_3_gt
    have h_zerofree_pos : 0 < zerofree_constant := zerofree_constant_pos

    have h_log_bound : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
      have h_ineq : |t| + 2 ≤ 2 * |t| := by linarith [ht]
      have h_log_ineq := Real.log_le_log (by linarith [abs_nonneg t] : 0 < |t| + 2) h_ineq
      rw [Real.log_mul (by norm_num) (ne_of_gt h_t_pos)] at h_log_ineq
      have h_log2_bound : Real.log 2 ≤ Real.log |t| :=
        Real.log_le_log (by norm_num) (by linarith [ht] : (2 : ℝ) ≤ |t|)
      linarith [h_log_ineq]

    have h_deltaz_eq : deltaz_t t = (zerofree_constant / 20) / Real.log (|t| + 2) := by
      simp [deltaz_t, deltaz]

    have h_main_bound : C_3 / deltaz_t t * Real.log |t| ≤
                        40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by
                                       
      rw [h_deltaz_eq]

      have h_div_rewrite : C_3 / ((zerofree_constant / 20) / Real.log (|t| + 2)) =
                          C_3 * Real.log (|t| + 2) * 20 / zerofree_constant := by
        field_simp [ne_of_gt h_zerofree_pos, ne_of_gt (Real.log_pos (by linarith [abs_nonneg t] : (1 : ℝ) < |t| + 2))]

      rw [h_div_rewrite]
                                                 
      have h_pos_factor : 0 ≤ C_3 * 20 / zerofree_constant :=
        div_nonneg (mul_nonneg (le_of_lt hC_3_pos) (by norm_num)) (le_of_lt h_zerofree_pos)

      calc C_3 * Real.log (|t| + 2) * 20 / zerofree_constant * Real.log |t|
          = C_3 * 20 / zerofree_constant * Real.log (|t| + 2) * Real.log |t| := by ring
      _ ≤ C_3 * 20 / zerofree_constant * (2 * Real.log |t|) * Real.log |t| := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_log_bound h_pos_factor)
                (le_of_lt h_log_t_pos)
      _ = 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by simp [pow_two]; ring

    calc (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ C_3 / deltaz_t t * Real.log |t| := h_bound
    _ ≤ 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := h_main_bound
    _ ≤ max (100 * C_3 / zerofree_constant) 2 * (Real.log |t|)^2 := by
        have h_factor_bound : 40 * C_3 / zerofree_constant ≤ max (100 * C_3 / zerofree_constant) 2 := by
          have h_coeff_ineq : 40 * C_3 ≤ 100 * C_3 := by
                                                                                     
            have h_coeff : (40 : ℝ) ≤ 100 := by norm_num
            exact mul_le_mul_of_nonneg_right h_coeff (le_of_lt hC_3_pos)
          have h_div_ineq : 40 * C_3 / zerofree_constant ≤ 100 * C_3 / zerofree_constant := by
                                          
            exact div_le_div_of_nonneg_right h_coeff_ineq (le_of_lt h_zerofree_pos)
          exact le_trans h_div_ineq (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right h_factor_bound (sq_nonneg _)

lemma lem_logDerivZetalogt0 :
  ∃ C > 1,
  ∀ (t : ℝ) (_ht : |t| > 3),
    ∀ s : ℂ, (1 - deltaz_t t) ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |t|^2 := by
                                                              
  obtain ⟨C_1, hC_1_gt, hC_1⟩ := lem_Zeta_Triangle_ZFR
  obtain ⟨C_4, hC_4_gt, hC_4⟩ := lem_sumKlogt2

  use C_1 + C_4

  constructor
  ·               
    linarith [hC_1_gt, hC_4_gt]

  ·              
    intro t ht s hs

    let c := (3/2 : ℂ) + I * t
    have hfin := lem_finiteKzeta t ht

    have h_triangle := hC_1 t ht hfin s hs

    have h_triangle_ineq := lem_triangle_ZFR t ht s hfin hs

    have h_sum_bound := hC_4 t ht hfin s hs

    have h_log_sq_ge : Real.log |t| ≤ Real.log |t|^2 := by
      have h_log_ge_one : (1 : ℝ) ≤ Real.log |t| := by
                                                         
        have h_t_gt_e : Real.exp 1 < |t| := by
          have h_e_bound : Real.exp 1 < 3 := by
                                                          
            simpa using lem_three_gt_e
          linarith [ht]
                                                                  
        have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_of_lt h_t_gt_e)
      have h_log_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
      rw [pow_two]
      exact le_mul_of_one_le_right (le_of_lt h_log_pos) h_log_ge_one

    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖ + C_1 * Real.log |t| := h_triangle
      _ ≤ (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖s - ρ‖) + C_1 * Real.log |t| := by
          apply add_le_add_left h_triangle_ineq
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t| := by
          apply add_le_add_left h_sum_bound
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t|^2 := by
                                                    
          have h_c1_nonneg : 0 ≤ C_1 := le_of_lt (lt_trans zero_lt_one hC_1_gt)
          exact add_le_add_right (mul_le_mul_of_nonneg_left h_log_sq_ge h_c1_nonneg) _
      _ = (C_4 + C_1) * Real.log |t|^2 := by ring
      _ = (C_1 + C_4) * Real.log |t|^2 := by ring

lemma lem_logDerivZetalogt2 :
  ∃ A: ℝ, A > 0 ∧ A < 1 ∧
  ∃ C > 1,
  ∀ (t : ℝ) (_ht : |t| > 3),
    ∀ s : ℂ, (1 - A / Real.log (abs t + 2) ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |t|^2 := by
  obtain ⟨C, hC_gt, hC_bound⟩ := lem_logDerivZetalogt0
  refine ⟨zerofree_constant / 20, ?Apos, ?Alt1, ⟨C, hC_gt, ?_⟩⟩
  ·         
    exact div_pos zerofree_constant_pos (by norm_num)
  ·         
    have hlt : zerofree_constant / 20 < (1 : ℝ) / 20 :=
      div_lt_div_of_pos_right zerofree_constant_lt_one (by norm_num)
    have : (1 : ℝ) / 20 < 1 := by norm_num
    exact lt_trans hlt this
  ·                                                                                
    intro t ht s hs
    have hδ : 1 - deltaz_t t ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t := by
      simpa [deltaz_t, deltaz, Complex.mul_I_im] using hs
    exact hC_bound t ht s hδ

lemma lem_rhoDRe4 :
  ∀ t : ℝ, ∀ z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t),
    z.re > 1 - 4 * deltaz_t t := by
  intro t z hz
                             
  have h_pos : 0 < deltaz_t t := by
                                                         
    have h_log_pos : 0 < Real.log (|t| + 2) := by
      have h1 : (1 : ℝ) < |t| + 2 := by
        have : (0 : ℝ) ≤ |t| := abs_nonneg _
        linarith
      exact Real.log_pos h1
    have h_num_pos : 0 < zerofree_constant / 20 := by
      have h20 : 0 < (20 : ℝ) := by norm_num
      exact div_pos zerofree_constant_pos h20
    have : 0 < (zerofree_constant / 20) / Real.log (|t| + 2) := by
      exact div_pos h_num_pos h_log_pos
    simpa [deltaz_t, deltaz, Complex.mul_I_im] using this

  have h_norm : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz

  have re_bound : |(z - (1 - deltaz_t t + t * Complex.I)).re| ≤ 2 * deltaz_t t :=
    (Complex.abs_re_le_norm _).trans h_norm

  have center_re : (1 - deltaz_t t + t * Complex.I).re = 1 - deltaz_t t := by
    calc (1 - deltaz_t t + t * Complex.I).re
      = (1 - deltaz_t t : ℂ).re + (t * Complex.I).re := by rw [Complex.add_re]
      _ = (1 - deltaz_t t) + (t * Complex.I).re := by simp [Complex.ofReal_re]
      _ = (1 - deltaz_t t) + 0 := by simp [Complex.mul_re, Complex.I_re]
      _ = 1 - deltaz_t t := by simp

  have re_simp : (z - (1 - deltaz_t t + t * Complex.I)).re = z.re - (1 - deltaz_t t) := by
    rw [Complex.sub_re, center_re]

  have re_bound' : |z.re - (1 - deltaz_t t)| ≤ 2 * deltaz_t t := by
    simpa [re_simp] using re_bound

  have lower_bound : z.re - (1 - deltaz_t t) ≥ -(2 * deltaz_t t) := by
    have h := (abs_le).1 re_bound'
    exact h.1

  have : z.re ≥ 1 - deltaz_t t - 2 * deltaz_t t := by linarith [lower_bound]
  have : z.re ≥ 1 - 3 * deltaz_t t := by linarith
  linarith [h_pos]

lemma helper_absIm_le_add_smallball (t : ℝ) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  |z.im| ≤ |t| + 2 * deltaz_t t := by
                                                                                     
  have hnorm : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
                                                                
  have h_im_diff : |(z - (1 - deltaz_t t + t * Complex.I)).im| ≤ 2 * deltaz_t t :=
    le_trans (Complex.abs_im_le_norm _) hnorm
                                             
  have center_im : (1 - deltaz_t t + t * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_im]
                                                 
  have diff_im : (z - (1 - deltaz_t t + t * Complex.I)).im = z.im - t := by
    simp [Complex.sub_im, center_im]
                            
  have h_im_sub : |z.im - t| ≤ 2 * deltaz_t t := by
    simpa [diff_im] using h_im_diff
                                                   
  have tri : |z.im| ≤ |z.im - t| + |t| := by
    simpa [sub_eq_add_neg] using! (abs_add_le (z.im - t) t)
                       
  have : |z.im - t| + |t| ≤ 2 * deltaz_t t + |t| := add_le_add_left h_im_sub _
  have hfinal : |z.im| ≤ 2 * deltaz_t t + |t| := le_trans tri this
  simpa [add_comm] using hfinal

lemma helper_log_le_two_log_smallball (t : ℝ) (ht : |t| > 3) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  Real.log (|z.im| + 2) ≤ 2 * Real.log (|t| + 2) := by
                                                                   
  have h_abs : |z.im| ≤ |t| + 2 * deltaz_t t :=
    helper_absIm_le_add_smallball t z hz
                        
  set a : ℝ := |t| + 2
  have h1 : |z.im| + 2 ≤ a + 2 * deltaz_t t := by
    have := add_le_add_left h_abs (2 : ℝ)
    simpa [a, add_comm, add_left_comm, add_assoc] using this
                                                 
  have ht2 : |t| > 2 := by linarith
  have hδ : 0 < deltaz_t t ∧ deltaz_t t < 1 / 9 := (lem_delta19).2 t ht2
  have hδlt : deltaz_t t < 1 / 9 := hδ.2
                      
  have h_two_delta_le_one : 2 * deltaz_t t ≤ 1 := by
    have hle : deltaz_t t ≤ 1 / 9 := le_of_lt hδlt
    have hmul : 2 * deltaz_t t ≤ 2 * (1 / 9 : ℝ) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    have : 2 * (1 / 9 : ℝ) ≤ 1 := by norm_num
    exact le_trans hmul this
  have h2 : a + 2 * deltaz_t t ≤ a + 1 := add_le_add_right h_two_delta_le_one a
                                 
  have ha_ge_two : (2 : ℝ) ≤ a := by
    have : 0 ≤ |t| := abs_nonneg t
    linarith [this]
  have ha_ge_one : (1 : ℝ) ≤ a := le_trans (by norm_num) ha_ge_two
  have h_a_plus_one_le_two_a : a + 1 ≤ a + a := by
    simpa using add_le_add_right ha_ge_one a
  have h_nonneg_a : 0 ≤ a := le_trans (by norm_num) ha_ge_two
  have h_2a_le_a2 : (2 : ℝ) * a ≤ a ^ 2 := by
    have : (2 : ℝ) * a ≤ a * a := mul_le_mul_of_nonneg_right ha_ge_two h_nonneg_a
    simpa [pow_two] using this
  have h_a1_le_a2 : a + 1 ≤ a ^ 2 :=
    le_trans h_a_plus_one_le_two_a (by simpa [two_mul] using h_2a_le_a2)
                                               
  have h_total : |z.im| + 2 ≤ a ^ 2 := le_trans (le_trans h1 h2) h_a1_le_a2
                    
  have hxpos : 0 < |z.im| + 2 := by
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
  have hlog := Real.log_le_log hxpos h_total
  calc
    Real.log (|z.im| + 2) ≤ Real.log (a ^ 2) := hlog
    _ = (2 : ℝ) * Real.log a := by simp
    _ = 2 * Real.log (|t| + 2) := by simp [a]

lemma helper_one_div_log_le_two_div_smallball (t : ℝ) (ht : |t| > 3) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  (1 : ℝ) / Real.log (|t| + 2) ≤ 2 / Real.log (|z.im| + 2) := by
                           
  have ht_pos1 : 1 < |t| + 2 := by linarith [abs_nonneg t]
  have hz_pos1 : 1 < |z.im| + 2 := by linarith [abs_nonneg z.im]
  have log_t_pos : 0 < Real.log (|t| + 2) := Real.log_pos ht_pos1
  have log_z_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos hz_pos1
                                                                 
  have h_norm : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have center_im : (1 - deltaz_t t + t * Complex.I).im = t := by
    simp [Complex.add_im]
  have diff_im : (z - (1 - deltaz_t t + t * Complex.I)).im = z.im - t := by
    simp [Complex.sub_im, center_im]
  have h1 : |z.im - t| ≤ ‖z - (1 - deltaz_t t + t * Complex.I)‖ := by
    simpa [diff_im] using Complex.abs_im_le_norm (z - (1 - deltaz_t t + t * Complex.I))
  have h2 : |z.im - t| ≤ 2 * deltaz_t t := h1.trans h_norm
  have hz_im_le : |z.im| ≤ |z.im - t| + |t| := by
                                                   
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using! abs_add_le (z.im - t) t
  have hz_im_le2 : |z.im| ≤ 2 * deltaz_t t + |t| := hz_im_le.trans (add_le_add_left h2 _)
  have hz_add2_le1 : |z.im| + 2 ≤ (2 * deltaz_t t + |t|) + 2 := add_le_add_left hz_im_le2 2
                                                     
  have hdelta_lt_one : deltaz_t t < 1 := by
    have hlt19 : deltaz_t t < 1 / 9 :=
      ((lem_delta19).2 t (by linarith : |t| > 2)).2
    exact lt_trans hlt19 (by norm_num)
  have h2delta_le_two : 2 * deltaz_t t ≤ 2 := by
    have hle : deltaz_t t ≤ 1 := le_of_lt hdelta_lt_one
    have := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)
    simpa using this
  have htwo_le : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have h2delta_le_tplus2 : 2 * deltaz_t t ≤ |t| + 2 := le_trans h2delta_le_two htwo_le
  have step_mid : (2 * deltaz_t t + |t|) + 2 ≤ ((|t| + 2) + |t|) + 2 := by
    have := add_le_add_left (add_le_add_left h2delta_le_tplus2 |t|) 2
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hz_plus2_le : |z.im| + 2 ≤ (|t| + 2) + |t| + 2 := le_trans hz_add2_le1 step_mid
  have hz_im_bound_final : |z.im| + 2 ≤ 2 * (|t| + 2) := by
                                                  
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hz_plus2_le
                           
  have hxpos : 0 < |z.im| + 2 := by linarith [abs_nonneg z.im]
  have hlog_step : Real.log (|z.im| + 2) ≤ Real.log (2 * (|t| + 2)) :=
    Real.log_le_log hxpos hz_im_bound_final
  have hlog_mul : Real.log (2 * (|t| + 2)) = Real.log 2 + Real.log (|t| + 2) := by
    have hneet : (|t| + 2) ≠ 0 := ne_of_gt (lt_trans (by norm_num) ht_pos1)
    simpa using Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hneet
  have hlog2_le_logt : Real.log 2 ≤ Real.log (|t| + 2) := by
    have h2lt : 0 < (2 : ℝ) := by norm_num
    have h2le : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    exact Real.log_le_log h2lt h2le
  have hlog_le_two : Real.log (|z.im| + 2) ≤ 2 * Real.log (|t| + 2) := by
    have : Real.log (|z.im| + 2) ≤ Real.log 2 + Real.log (|t| + 2) := by
      simpa [hlog_mul] using hlog_step
    have : Real.log (|z.im| + 2) ≤ Real.log (|t| + 2) + Real.log (|t| + 2) :=
      this.trans (add_le_add_left hlog2_le_logt _)
    simpa [two_mul] using this
                                           
  have h' : 1 * Real.log (|z.im| + 2) ≤ 2 * Real.log (|t| + 2) := by
    simpa [one_mul] using hlog_le_two
  simpa [one_mul] using (div_le_div_iff₀ log_t_pos log_z_pos).mpr h'

lemma helper_deltaz_t_le_two_deltaz_smallball (t : ℝ) (ht : |t| > 3) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  deltaz_t t ≤ 2 * deltaz z := by
                                                              
  have h_recip := helper_one_div_log_le_two_div_smallball t ht z hz

  have hpos_const : 0 ≤ zerofree_constant / 20 := by
    have hpos : 0 < zerofree_constant := zerofree_constant_pos
    have h20 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt hpos) (le_of_lt h20)

  have h_mul := mul_le_mul_of_nonneg_left h_recip hpos_const

  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
              simp [deltaz_t, deltaz]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by
              simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (2 / Real.log (|z.im| + 2)) := by
              simpa [one_div, div_eq_mul_inv] using h_mul
    _ = 2 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
              ring
    _ = 2 * deltaz z := by
              simp [deltaz, div_eq_mul_inv]

lemma lem_DRez6dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t),
    z.re ≥ 1 - 6 * deltaz z := by
  intro t ht z hz
                                                                      
  have h_ball : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
                                                       
  have h_re_absle : |(z - (1 - deltaz_t t + t * Complex.I)).re| ≤ 2 * deltaz_t t :=
    (Complex.abs_re_le_norm _).trans h_ball
  have h_re_absle' : |z.re - (1 - deltaz_t t)| ≤ 2 * deltaz_t t := by
    simpa [Complex.sub_re] using h_re_absle
                                    
  have h_lower : z.re - (1 - deltaz_t t) ≥ -(2 * deltaz_t t) := by
    have := (abs_le).1 h_re_absle'
    exact this.1
                               
  have h3 : z.re ≥ 1 - 3 * deltaz_t t := by
    linarith
                              
  have h_dt_le : deltaz_t t ≤ 2 * deltaz z :=
    helper_deltaz_t_le_two_deltaz_smallball t ht z hz
                                        
  have h_mult : 3 * deltaz_t t ≤ 6 * deltaz z := by
    have h := mul_le_mul_of_nonneg_left h_dt_le (by norm_num : (0 : ℝ) ≤ 3)
    calc
      3 * deltaz_t t ≤ 3 * (2 * deltaz z) := h
      _ = 6 * deltaz z := by ring
                                
  have h_final : 1 - 3 * deltaz_t t ≥ 1 - 6 * deltaz z := by
    linarith [h_mult]
                                                            
  exact le_trans h_final h3

lemma lem_YinD :
  ∀ t : ℝ, |t| > 3 →
    Yt t (deltaz_t t) ⊆ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t) := by
  intro t ht z hz
  rcases hz with ⟨hzero, habs⟩
  have hdist : dist z (1 - deltaz_t t + t * Complex.I) ≤ 2 * deltaz_t t := by
    simpa [Complex.dist_eq] using habs
  exact Metric.mem_closedBall.mpr hdist

theorem lem_rhoYzero (t : ℝ) (δ : ℝ) (ρ_1 : ℂ) (h_rho_1_in_Yt : ρ_1 ∈ Yt t δ) :
    riemannZeta ρ_1 = 0 := by
                                
  unfold Yt at h_rho_1_in_Yt
                                                                                       
  exact h_rho_1_in_Yt.1

theorem lem_absReabs (w : ℂ) : |w.re| ≤ ‖w‖ := by
  exact Complex.abs_re_le_norm w

theorem lem_zRe (t : ℝ) (δ : ℝ) (z : ℂ) : |(z - (1 - δ + t * Complex.I)).re| ≤ ‖(z - (1 - δ + t * Complex.I))‖ := by
  apply lem_absReabs

theorem lem_zRe2 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |(z - (1 - δ + t * Complex.I)).re| ≤ 2 * δ := by
  have h1 : |(z - (1 - δ + t * Complex.I)).re| ≤ ‖(z - (1 - δ + t * Complex.I))‖ := lem_zRe t δ z
  exact le_trans h1 h_le

theorem lem_Rezit (t : ℝ) (δ : ℝ) (z : ℂ) :
    (z - (1 - δ + t * Complex.I)).re = z.re - (1 - δ) := by
  rw [Complex.sub_re]
                                             
  rw [Complex.add_re]
                                                  
  rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
                                             
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
                                          
  simp

theorem lem_zRe3 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |z.re - (1 - δ)| ≤ 2 * δ := by
                                                
  have h1 : |(z - (1 - δ + t * Complex.I)).re| ≤ 2 * δ :=
    lem_zRe2 t δ z h_le
                                     
  have hRe : (z - (1 - δ + t * Complex.I)).re = z.re - (1 - δ) :=
    lem_Rezit t δ z
  simpa [hRe] using h1

theorem lem_negleabs (a : ℝ) (b : ℝ) (h_abs : |a| ≤ b) : a ≥ -b := by
  rw [abs_le] at h_abs
  exact h_abs.1

theorem lem_absrez1d (δ : ℝ) (z : ℂ)
    (h_le : |z.re - (1 - δ)| ≤ 2 * δ) :
    z.re - (1 - δ) ≥ - (2 * δ) := by
  exact lem_negleabs (z.re - (1 - δ)) (2 * δ) h_le

theorem lem_absrez1d2 (δ : ℝ) (z : ℂ)
    (h_le : |z.re - (1 - δ)| ≤ 2 * δ) :
    z.re ≥ 1 - 3 * δ := by
                                          
  have hneg : z.re - (1 - δ) ≥ - (2 * δ) :=
    lem_absrez1d δ z h_le
                                                
  have : z.re ≥ 1 - δ - 2 * δ := by linarith
                                   
  convert this using 1
  ring
theorem lem_absrez1d3 (δ : ℝ) (z : ℂ) (hδ : δ > 0)
    (h_le : |z.re - (1 - δ)| ≤ 2 * δ) :
    z.re > 1 - 4 * δ := by
  have h1 : z.re ≥ 1 - 3 * δ := lem_absrez1d2 δ z h_le
  linarith [h1, hδ]

theorem lem_zRe4 (t : ℝ) (δ : ℝ) (hδ : δ > 0) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    z.re > 1 - 4 * δ := by
  have h1 : |z.re - (1 - δ)| ≤ 2 * δ := lem_zRe3 t δ z h_le
  exact lem_absrez1d3 δ z hδ h1

lemma riemannZeta_no_zeros_left_halfplane_off_real_axis (s : ℂ) (h_re : s.re ≤ 0) (h_im : s.im ≠ 0) : riemannZeta s ≠ 0 := by
                               
  intro h_zero

  have hs_not_neg_nat : ∀ n : ℕ, s ≠ -n := by
    intro n h_eq
                                                   
    have : s.im = 0 := by
      rw [h_eq]
      rw [Complex.neg_im]
      simp
    exact h_im this

  have hs_not_one : s ≠ 1 := by
    intro h_eq
                                                      
    have : s.re = 1 := by
      rw [h_eq]
      exact Complex.one_re
    linarith [h_re, this]

  have functional_eq := riemannZeta_one_sub hs_not_neg_nat hs_not_one

  rw [h_zero] at functional_eq
  simp at functional_eq

  have h1s_re_ge_1 : (1 - s).re ≥ 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [h_re]

  have h1s_nonzero : riemannZeta (1 - s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    exact h1s_re_ge_1

  exact h1s_nonzero functional_eq

lemma lem_Imzit (t : ℝ) (δ : ℝ) (z : ℂ) :
    (z - (1 - δ + t * Complex.I)).im = z.im - t := by
  have him : (1 - δ + t * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_im]
  simp [Complex.sub_im, him]

lemma lem_zIm2 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |(z - (1 - δ + t * Complex.I)).im| ≤ 2 * δ := by
  have : |(z - (1 - δ + t * Complex.I)).im| ≤ ‖(z - (1 - δ + t * Complex.I))‖ :=
    Complex.abs_im_le_norm (z - (1 - δ + t * Complex.I))
  exact le_trans this h_le

lemma lem_zIm3 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |z.im - t| ≤ 2 * δ := by
  have h1 : |(z - (1 - δ + t * Complex.I)).im| ≤ 2 * δ :=
    lem_zIm2 t δ z h_le
  have him : (z - (1 - δ + t * Complex.I)).im = z.im - t :=
    lem_Imzit t δ z
  simpa [him] using h1

lemma abs_le_add_of_abs_sub_le {a b ε : ℝ} (h : |a - b| ≤ ε) :
  |a| ≤ |b| + ε := by
  calc
    |a| = |b + (a - b)| := by
      simp [sub_eq_add_neg, add_left_comm]
    _ ≤ |b| + |a - b| := by
      simpa [sub_eq_add_neg] using! abs_add_le b (a - b)
    _ ≤ |b| + ε := by
      exact add_le_add_right h _

lemma log_add_lt_log_add_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  Real.log (x + y) < Real.log x + y / x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hxy_pos : 0 < x + y := add_pos hx hy
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy_pos
  have hy_div_pos : 0 < y / x := div_pos hy hx
  have hdiv_eq : (x + y) / x = 1 + y / x := by
    have : (x + y) / x = x / x + y / x := by simp [add_div]
    simpa [div_self hxne] using this
  have hgt1 : 1 < (x + y) / x := by
    have : 1 < 1 + y / x := by linarith [hy_div_pos]
    simpa [hdiv_eq] using this
  have hposu : 0 < (x + y) / x := lt_trans zero_lt_one hgt1
  have hne1 : (x + y) / x ≠ 1 := ne_of_gt hgt1
  have hloglt : Real.log ((x + y) / x) < (x + y) / x - 1 :=
    Real.log_lt_sub_one_of_pos hposu hne1
  have hrhs : (x + y) / x - 1 = y / x := by
    have : (1 + y / x) - 1 = y / x := by
      simp
    simp [hdiv_eq]
  have hldiv : Real.log ((x + y) / x) = Real.log (x + y) - Real.log x :=
    Real.log_div hxy_ne hxne
  have hcore : Real.log (x + y) - Real.log x < y / x := by
    simpa [hldiv, hrhs] using hloglt
  have := add_lt_add_left hcore (Real.log x)
  simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using this

lemma abs_le_add_of_abs_sub_le' {a b ε : ℝ} (h : |a - b| ≤ ε) :
  |a| ≤ |b| + ε := by
  calc
    |a| = |b + (a - b)| := by
      simp [sub_eq_add_neg, add_left_comm]
    _ ≤ |b| + |a - b| := by
      simpa [sub_eq_add_neg] using! abs_add_le b (a - b)
    _ ≤ |b| + ε := by
      exact add_le_add_right h _

lemma delta_half_eq (c t : ℝ) :
  ((c / 2) / Real.log (|t| + 2)) / 2 = (c / 4) / Real.log (|t| + 2) := by
                                                                                           
  have hx :
      ((c * (1 / 2)) * ((Real.log (|t| + 2))⁻¹)) * (1 / 2)
        = (c * (1 / 4)) * ((Real.log (|t| + 2))⁻¹) := by
    ring
  simpa [div_eq_mul_inv] using hx

lemma log_abs_im_le (t t1 δ : ℝ) (h : |t1 - t| ≤ δ) :
  Real.log (|t1| + 2) ≤ Real.log (|t| + 2) + δ / (|t| + 2) := by
                                       
  have hx1pos : 0 < |t1| + 2 := by
    have : (0 : ℝ) ≤ |t1| := abs_nonneg t1
    linarith
  have hxpos : 0 < |t| + 2 := by
    have : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have hxnonneg : 0 ≤ |t| + 2 := le_of_lt hxpos
                                                            
  have habs : |t1| ≤ |t| + |t1 - t| := by
    have htri : |(t1 - t) + t| ≤ |t1 - t| + |t| := abs_add_le (t1 - t) t
    simpa [sub_add_cancel, add_comm] using htri
                                      
  have hxy : |t1| + 2 ≤ (|t| + 2) + |t1 - t| := by
    have := add_le_add_left habs 2
    simpa [add_comm, add_left_comm, add_assoc] using this
                        
  have hlog1 : Real.log (|t1| + 2) ≤ Real.log ((|t| + 2) + |t1 - t|) :=
    Real.log_le_log hx1pos hxy
                                                             
  have hy_nonneg : 0 ≤ |t1 - t| := abs_nonneg (t1 - t)
  have hlog2 : Real.log ((|t| + 2) + |t1 - t|)
      ≤ Real.log (|t| + 2) + |t1 - t| / (|t| + 2) := by
    by_cases hpos :  0 < |t1 - t|
    · exact le_of_lt (log_add_lt_log_add_div hxpos hpos)
    · have heq : |t1 - t| = 0 := le_antisymm (le_of_not_gt hpos) hy_nonneg
      have : Real.log (|t| + 2) ≤ Real.log (|t| + 2) := le_rfl
      simp [heq]
                                                        
  have hdiv : |t1 - t| / (|t| + 2) ≤ δ / (|t| + 2) :=
    div_le_div_of_nonneg_right h hxnonneg
  have hadd := add_le_add_right hdiv (Real.log (|t| + 2))
  exact le_trans (le_trans hlog1 hlog2) hadd

lemma combine_re_bounds_to_c_over_log_le {ρre c δ L1 : ℝ}
  (h_ge : ρre ≥ 1 - (3 / 2) * δ) (h_le : ρre ≤ 1 - c / L1) :
  c / L1 ≤ (3 / 2) * δ := by
                                  
  have h : 1 - (3 / 2) * δ ≤ 1 - c / L1 := le_trans h_ge h_le
                               
  have h' := sub_le_sub_right h (1 : ℝ)
             
  have h'' : -((3 / 2) * δ) ≤ -(c / L1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
                          
  simpa using (neg_le_neg_iff.mp h'')

lemma core_contradiction2 {L t c δ : ℝ}
  (hLpos : 0 < L) (hpos : 0 < |t| + 2)
  (hδ : δ = (c / 2) / L)
  (h : L ≤ (3 / 2) * δ / (|t| + 2)) :
  L ^ 2 * (|t| + 2) ≤ 3 * c / 4 := by
                                         
  have h1' := (mul_le_mul_of_nonneg_right h (le_of_lt hpos))
                                 
  have hbne : (|t| + 2) ≠ 0 := ne_of_gt hpos
  have rhs_eq : ((3 / 2) * δ / (|t| + 2)) * (|t| + 2) = (3 / 2) * δ := by
    calc
      ((3 / 2) * δ / (|t| + 2)) * (|t| + 2)
          = ((3 / 2) * δ) * ((1 / (|t| + 2)) * (|t| + 2)) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = ((3 / 2) * δ) * 1 := by
            simp [hbne]
      _ = (3 / 2) * δ := by
            ring
  have h1 : L * (|t| + 2) ≤ (3 / 2) * δ := by
    simpa [rhs_eq] using h1'
                                 
  have h2 := (mul_le_mul_of_nonneg_left h1 (le_of_lt hLpos))
  have h3 : L ^ 2 * (|t| + 2) ≤ (3 / 2) * (δ * L) := by
    simpa [pow_two, mul_left_comm, mul_assoc, mul_comm] using h2
                                             
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hδL : δ * L = c / 2 := by
    calc
      δ * L = ((c / 2) / L) * L := by simp [hδ]
      _ = (c / 2) * ((L⁻¹) * L) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = (c / 2) * 1 := by
        simp [hLne]
      _ = c / 2 := by simp
  have h4 : L ^ 2 * (|t| + 2) ≤ (3 / 2) * (c / 2) := by
    simpa [hδL] using h3
                                 
  have h5 : (3 / 2 : ℝ) * (c / 2) = 3 * c / 4 := by
    ring
  simpa [h5] using h4

lemma abs_lower_bound_sub (x y : ℝ) : |x| ≥ |y| - |x - y| := by
                                                        
  have h' : |y| ≤ |x| + |y - x| := by
    have htriv : |y - x| ≤ |y - x| := le_rfl
    simpa [sub_eq_add_neg] using
      (abs_le_add_of_abs_sub_le' (a := y) (b := x) (ε := |y - x|) htriv)
                               
  have h1 : |y| ≤ |x| + |x - y| := by simpa [abs_sub_comm] using h'
                                       
  simpa [ge_iff_le] using (sub_le_iff_le_add).2 h1

lemma abs_im_ge_T0_from_close {t : ℝ} {ρ : ℂ} {δ T0 : ℝ}
  (hclose : |ρ.im - t| ≤ 2 * δ) (hineq : |t| - 2 * δ ≥ T0) :
  T0 ≤ |ρ.im| := by
  have h1 : |ρ.im| ≥ |t| - |ρ.im - t| := by
    simpa [sub_eq_add_neg, abs_sub_comm] using (abs_lower_bound_sub ρ.im t)
  have : |ρ.im| ≥ |t| - 2 * δ := by
    exact ge_trans h1 (by
                                                                   
      gcongr)
  exact le_trans hineq this

lemma lem_Kzetaempty :
  ∀ t : ℝ, |t| > 3 →
    Yt t (deltaz_t t) = ∅ := by
  intro t ht
                                                                  
  rw [Set.eq_empty_iff_forall_notMem]
  intro ρ_1 h_mem

  have h_zero : riemannZeta ρ_1 = 0 := lem_rhoYzero t (deltaz_t t) ρ_1 h_mem

  have h_norm : ‖ρ_1 - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    exact h_mem.2

  have h_im_bound : |ρ_1.im - t| ≤ 2 * deltaz_t t := by
    exact lem_zIm3 t (deltaz_t t) ρ_1 h_norm

  have h_delta_small : deltaz_t t < 1/9 := by
    have h_bounds := lem_delta19
    exact (h_bounds.2 t (by linarith [ht])).2

  have h_im_large : 2 < |ρ_1.im| := by
                                                               
    have h_tri : |ρ_1.im| ≥ |t| - |ρ_1.im - t| := by
      exact abs_lower_bound_sub ρ_1.im t
    have h_bound : |ρ_1.im| ≥ |t| - 2 * deltaz_t t := by
      exact ge_trans h_tri (by gcongr)
    have h_small_delta : 2 * deltaz_t t < 2/9 := by
      linarith [h_delta_small]
    have h_final : |t| - 2 * deltaz_t t > 3 - 2/9 := by
      linarith [ht, h_small_delta]
    have h_gt_2 : 3 - 2/9 > 2 := by norm_num
    linarith [h_bound, h_final, h_gt_2]

  have h_in_ball : ρ_1 ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t) := by
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using! h_norm)

  have h_re_bound : ρ_1.re ≥ 1 - 6 * deltaz ρ_1 := by
    exact lem_DRez6dz t ht ρ_1 h_in_ball

  have h_delta_pos : 0 < deltaz ρ_1 := by
    have h_bounds := lem_delta19
    exact (h_bounds.1 ρ_1 (by linarith [h_im_large])).1

  have h_re_strict : ρ_1.re > 1 - 9 * deltaz ρ_1 := by
    linarith [h_re_bound, h_delta_pos]

  have h_nonzero : riemannZeta ρ_1 ≠ 0 := by
    exact lem_ZFRdelta ρ_1 h_im_large h_re_strict

  exact h_nonzero h_zero

lemma Yt_subset_closedBall (t : ℝ) (δ : ℝ) :
    Yt t δ ⊆ Metric.closedBall (1 - δ + t * Complex.I) (2 * δ) := by
                                               
  intro ρ_1 hρ_1

  unfold Yt at hρ_1
                                                                          
  obtain ⟨_, h_abs⟩ := hρ_1
                                   
  rw [Metric.mem_closedBall]
                                              
  rw [Complex.dist_eq]
                                  
  exact h_abs

lemma Yt_finite (t : ℝ) (δ : ℝ) : (Yt t δ).Finite := by
                                          
  have h_subset := Yt_subset_closedBall t δ

  let K := Metric.closedBall (1 - δ + t * Complex.I) (2 * δ)
  have h_compact : IsCompact K := closedBall_compact_complex (1 - δ + t * Complex.I) (2 * δ)

  have h_zeros_finite := riemannZeta_zeros_finite_of_compact K h_compact

  have h_sub : Yt t δ ⊆ {z ∈ K | riemannZeta z = 0} := by
    intro ρ hρ

    constructor
    ·                               
      exact h_subset hρ
    ·                     
      unfold Yt at hρ
      exact hρ.1

  exact Set.Finite.subset h_zeros_finite h_sub

lemma lem_sumempty (g : ℂ → ℂ) : (∑ s ∈ (∅ : Finset ℂ), g s) = 0 := by
  rfl

lemma lem_Ksumempty :
  ∀ t : ℝ, |t| > 3 →
    (∑ ρ_1 ∈ (Yt_finite t (deltaz_t t)).toFinset, ((analyticOrderAt riemannZeta ρ_1).toNat : ℂ) / (1 - (deltaz_t t) + t * Complex.I - ρ_1)) = 0 := by
  intro t ht
                                                       
  have h_empty : Yt t (deltaz_t t) = ∅ := lem_Kzetaempty t ht
                                                                                                             
  have h_finset_empty : (Yt_finite t (deltaz_t t)).toFinset = ∅ := by
    rw [Set.Finite.toFinset_eq_empty]
    exact h_empty
                       
  rw [h_finset_empty]
  exact lem_sumempty _

lemma norm_div_cast_vonMangoldt (s : ℂ) :
  (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ s)‖)
  = (fun n : ℕ => (|ArithmeticFunction.vonMangoldt n|) / ‖(n : ℂ) ^ s‖) := by
  funext n
  simp [Complex.norm_real, Real.norm_eq_abs]

lemma ArithmeticFunction.summable_vonMangoldt_norm_rw {s : ℂ} :
  Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ s)‖)
  ↔ Summable (fun n : ℕ => (|ArithmeticFunction.vonMangoldt n|) / ‖(n : ℂ) ^ s‖) := by
  classical
  have hfun :
      (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ s)‖)
        = (fun n : ℕ => (|ArithmeticFunction.vonMangoldt n|) / ‖(n : ℂ) ^ s‖) := by
    funext n
    simp [Complex.norm_real, div_eq_mul_inv]
  simp

lemma lem_norm_cpow_nat (n : ℕ) (s : ℂ) (hn : 1 ≤ n) : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
  have hpos : 0 < (n : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hn)
  simpa using (Complex.norm_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) hpos s)

lemma lem_vonMangoldt_nonneg (n : ℕ) : 0 ≤ (ArithmeticFunction.vonMangoldt n) := by
  simp

lemma lem_term_real_nonneg (n : ℕ) (σ : ℝ) (_hσ : 1 < σ) : ∃ r ≥ (0:ℝ), ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r : ℂ) := by
                                                     
  let r : ℝ := (ArithmeticFunction.vonMangoldt n) / ((n : ℝ) ^ σ)
  refine ⟨r, ?_, ?_⟩
  ·                                                                                      
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_nonneg : 0 ≤ (n : ℝ) ^ σ := by
      simpa using (Real.rpow_nonneg hbase_nonneg σ)
                                          
    have hv_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n) := by
      simp
    have : 0 ≤ (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ σ)⁻¹ :=
      mul_nonneg hv_nonneg (inv_nonneg.mpr hden_nonneg)
    simpa [r, div_eq_mul_inv] using this
  ·                                            
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_eq : (((n : ℝ) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ (σ : ℂ) := by
      simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hbase_nonneg) (y := σ))
    calc
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ)))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) := by
              simp [hden_eq.symm]
      _ = (((ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) ^ σ)) : ℝ) := by
              simp
      _ = (r : ℂ) := by rfl

lemma lem_tsum_norm_vonMangoldt_depends_on_Re (s : ℂ) (σ : ℝ) (hσ : σ = s.re) (_hs : 1 < s.re) :
  (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ s)‖) =
  (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  classical
                                            
  have hfun : (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ s)‖)
            = (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n
    by_cases h0 : n = 0
    ·                                                         
      subst h0
      simp [ArithmeticFunction.vonMangoldt]
      simp only [_root_.ite_eq_right (not_isPrimePow_zero (R := ℕ)), abs_zero, zero_div]
    ·                                                                                       
      have hn0C : (n : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.cast_ne_zero.mpr h0)
      have harg : Complex.arg (n : ℂ) = 0 := by
        have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        simp
                          
      have hden_s : ‖(n : ℂ) ^ s‖ = ‖(n : ℂ)‖ ^ s.re := by
                                                    
        simpa [harg, Real.exp_zero, div_one] using
          (Complex.norm_cpow_of_ne_zero (z := (n : ℂ)) (w := s) hn0C)
      have hden_σ : ‖(n : ℂ) ^ (σ : ℂ)‖ = ‖(n : ℂ)‖ ^ σ := by
        simp
                                         
      simp [hden_s, hσ]
                                                       
  have htsum := congrArg (fun f : ℕ → ℝ => (∑' n, f n)) hfun
  simpa using htsum

lemma helper_LSeries_vonMangoldt_tsum (σ : ℝ) (hσ : 1 < σ) :
  (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) =
  - deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h0 : ((fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) 0) = 0 := by simp
  simpa [LSeries, LSeries.term_def₀ (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) h0,
        Complex.cpow_neg, div_eq_mul_inv] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (σ : ℂ)) hs)

lemma summable_ofReal_iff {f : ℕ → ℝ} : Summable (fun n => (f n : ℂ)) ↔ Summable f := by
  simp

lemma helper_summable_of_summable_norm {u : ℕ → ℂ}
  (h : Summable (fun n => ‖u n‖)) : Summable u := by
  simpa using (Summable.of_norm (f := u) h)

lemma helper_norm_tsum_eq_tsum_norm_of_nonneg_real {u : ℕ → ℂ} {r : ℕ → ℝ}
  (h : ∀ n, u n = (r n : ℂ)) (hr : ∀ n, 0 ≤ r n) (_hu : Summable u) :
  ‖(∑' n, u n)‖ = ∑' n, ‖u n‖ := by
  classical
                                                      
  have hsum_eq_ofReal : (∑' n, (r n : ℂ)) = ((∑' n, r n : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_tsum r).symm
  have hrewrite_u : ‖∑' n, u n‖ = ‖∑' n, (r n : ℂ)‖ := by
    have hfun : u = (fun n => (r n : ℂ)) := funext h
    simp [hfun]
  have hnorm_abs : ‖((∑' n, r n : ℝ) : ℂ)‖ = |∑' n, r n| := by
    simp [Real.norm_eq_abs]
                                     
  have hLHS : ‖∑' n, u n‖ = |∑' n, r n| := by
    simp [hrewrite_u, hsum_eq_ofReal]
                                                               
  have hsum_nonneg : 0 ≤ ∑' n, r n := tsum_nonneg hr
  have habs_sum : |∑' n, r n| = ∑' n, r n := abs_of_nonneg hsum_nonneg
                                  
  have hfunEq : (fun n => ‖u n‖) = (fun n => ‖(r n : ℂ)‖) := by
    funext n; simp [h n]
  have hfunEq2 : (fun n => ‖(r n : ℂ)‖) = (fun n => r n) := by
    funext n
    have : ‖(r n : ℂ)‖ = ‖r n‖ := by simp
    have : ‖r n‖ = |r n| := by simp
    have : |r n| = r n := abs_of_nonneg (hr n)
    simp [this]
  have hsum_norms1 : (∑' n, ‖u n‖) = ∑' n, ‖(r n : ℂ)‖ :=
    congrArg (fun f : ℕ → ℝ => ∑' n, f n) hfunEq
  have hsum_norms2 : (∑' n, ‖(r n : ℂ)‖) = ∑' n, r n :=
    congrArg (fun f : ℕ → ℝ => ∑' n, f n) hfunEq2
  have hRHS : (∑' n, ‖u n‖) = ∑' n, r n := hsum_norms1.trans hsum_norms2
                                       
  calc
    ‖(∑' n, u n)‖ = |∑' n, r n| := hLHS
    _ = ∑' n, r n := habs_sum
    _ = ∑' n, ‖u n‖ := by simp [hRHS]

lemma lem_norm_logDeriv_le_tsum (s : ℂ) (hs : 1 < s.re) :
  ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := by
  classical
                                                      
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                  
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs)
                                                                                
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    (summable_norm_iff).mpr hsum_term
                                                                            
  have hEq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [f] using! (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs)
                                                                                         
  have hpoint : (fun n : ℕ => ‖LSeries.term f s n‖)
                = (fun n : ℕ => ‖f n / ((n : ℂ) ^ s)‖) := by
    funext n
    by_cases h0 : n = 0
    ·                              
      subst h0
                                                
      have hf0r : ArithmeticFunction.vonMangoldt 0 = 0 := by
        simp
      have hf0 : f 0 = 0 := by simp [f, hf0r]
      simp [LSeries.term, f, hf0]
    ·                                              
      simp [LSeries.term, f, h0]
                                                      
  calc
    ‖deriv riemannZeta s / riemannZeta s‖
        = ‖- deriv riemannZeta s / riemannZeta s‖ := by simp [norm_neg]
    _ = ‖∑' n : ℕ, LSeries.term f s n‖ := by simp [hEq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
          norm_tsum_le_tsum_norm (f := fun n : ℕ => LSeries.term f s n) hsum_norm
    _ = ∑' n : ℕ, ‖f n / ((n : ℂ) ^ s)‖ := by simp [hpoint]
    _ = ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := rfl

lemma lem_tsum_norm_vonMangoldt_depends_on_Re_cast (s : ℂ) (σ : ℝ)
  (hσ : σ = s.re) (hs : 1 < s.re) :
  (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
    = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
                       
  have hre_ne_zero : s.re ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hσ_ne_zero : σ ≠ 0 := by
    have : 0 < σ := by simpa [hσ] using (lt_trans zero_lt_one hs)
    exact ne_of_gt this
                                                                                
  have hterm : (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
      = (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n
                                                             
    have hden_s : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n hre_ne_zero
    have hden_σ : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ (σ : ℂ).re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa [Complex.ofReal_re] using hσ_ne_zero)
    calc
      ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖
          = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ s‖ := by simp
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ s.re) := by
            simp [hden_s, Complex.norm_real]
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ σ) := by simp [hσ]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            simp [hden_σ, Complex.ofReal_re, Complex.norm_real]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖ := by simp
  simpa using congrArg (fun f : ℕ → ℝ => ∑' n, f n) hterm

lemma helper_norm_neg_logDeriv_eq_tsum_norm (σ : ℝ) (hσ : 1 < σ) :
  ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ =
    (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  classical
                                  
  let s : ℂ := (σ : ℂ)
                                                                             
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                     
  let u : ℕ → ℂ := fun n => LSeries.term f s n
                                                   
  have hs_re : 1 < s.re := by simpa using! hσ
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs_re)
                       
  have hsum_u : Summable u := hsum_term
                                                        
  have hL_eq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs_re)
  have hsum_eq : (∑' n, u n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [u] using hL_eq

  have hterm_as_div : ∀ n,
      u n = ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) := by
    intro n; by_cases h0 : n = 0
    ·         
      subst h0; simp [u, LSeries.term, f, s]
    ·         
      simp [u, LSeries.term, f, s, h0]
                                                           
  let r : ℕ → ℝ := fun n => Classical.choose (lem_term_real_nonneg n σ hσ)
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).1
  have hr_cast : ∀ n,
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r n : ℂ) := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).2
  have hr_eq' : ∀ n, u n = (r n : ℂ) := by
    intro n; simpa [hterm_as_div n] using (hr_cast n)
                                       
  have hsum_rc : Summable (fun n => (r n : ℂ)) := by
    simpa [u, hr_eq'] using hsum_u
  have hsum_r : Summable r := (Complex.summable_ofReal).1 hsum_rc
                                                         
  have hsum_u_as_real : (∑' n, u n) = ((∑' n, r n) : ℝ) := by
    have hru : (fun n => (r n : ℂ)) = u := by
      funext n; symm; exact hr_eq' n
    have := (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := r))

    simpa [hru] using this.symm
                                                             
  have hpoint_norm : (fun n : ℕ => ‖u n‖)
        = (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n; by_cases h0 : n = 0
    · subst h0; simp [u, LSeries.term, f, s]
    · simp [u, LSeries.term, f, s, h0]
  have hnorm_fun : (fun n : ℕ => ‖u n‖) = r := by
    funext n; simp [hr_eq' n, Complex.norm_real, abs_of_nonneg (hr_nonneg n)]
  have hsum_norm : Summable (fun n : ℕ => ‖u n‖) := by
    simpa [hnorm_fun] using hsum_r
                                                        
  have hineq : ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ :=
    norm_tsum_le_tsum_norm (f := u) hsum_norm
                                                  
  set S : ℝ := ∑' n, r n
  have hS_le : ‖((S : ℝ) : ℂ)‖ ≤ S := by
    simpa [S, hsum_u_as_real, hnorm_fun] using hineq
                              
  have hS_nonneg : 0 ≤ S := by
    have habs_le : |S| ≤ S := by simpa [Complex.norm_real] using hS_le
    exact (abs_nonneg S).trans habs_le
                                                
  have h_left : ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
      = ‖∑' n, u n‖ := by
    have : - deriv riemannZeta s / riemannZeta s = ∑' n, u n := by simpa [hsum_u_as_real] using hsum_eq.symm
    simp [s, this]
  have h_mid : ‖∑' n, u n‖ = S := by
                                               
    have : ‖((S : ℝ) : ℂ)‖ = S := by simp [Complex.norm_real, abs_of_nonneg hS_nonneg]
    simpa [S, hsum_u_as_real] using this
  have h_right : (∑' n : ℕ, ‖u n‖) = S := by simp [S, hnorm_fun]
                                            
  calc
    ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = ‖∑' n, u n‖ := h_left
    _ = S := h_mid
    _ = (∑' n : ℕ, ‖u n‖) := h_right.symm
    _ = (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
          simp [hpoint_norm]

theorem lem_zetacenterbd :
  ∀ t : ℝ,
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤
      ‖deriv riemannZeta σ / riemannZeta σ‖ := by
  intro t σ hσge
                   
  set s : ℂ := Complex.mk σ t
                                                  
  have hs : 1 < s.re := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  have hσgt1 : 1 < σ := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
                                                           
  have h_le_sum := lem_norm_logDeriv_le_tsum s hs
  have h1 : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := by
    simpa [norm_div, Complex.norm_real] using h_le_sum
                                                                                       
  have h_dep :
      (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
                    
    have hre : σ = s.re := by simp [s]
    simpa using (lem_tsum_norm_vonMangoldt_depends_on_Re_cast s σ hre hs)
  have h_dep_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖)
        = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := by
    simpa [norm_div, Complex.norm_real] using h_dep
                                                            
  have h_sum_eq_norm :
      ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) :=
    helper_norm_neg_logDeriv_eq_tsum_norm σ hσgt1
  have h_sum_eq_norm_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖)
        = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    simpa [norm_div, Complex.norm_real] using h_sum_eq_norm.symm
                                      
  have h_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := h1
      _ = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := h_dep_ratio
      _ = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := h_sum_eq_norm_ratio
                                                          
  simpa [s, norm_neg] using h_main

lemma lem_logDerivZetalogt32 :
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C := by
                                                        
  obtain ⟨C0, hC0_gt1, hC0_bound⟩ := Z0bound_const
                                            
  refine ⟨C0 + 2, by linarith, ?_⟩
  intro t ht σ hσ
                                                   
  have h_center := lem_zetacenterbd t σ hσ
                                  
  set δ : ℝ := σ - 1
  have hδ_pos : 0 < δ := by linarith [hσ]
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by linarith [hσ]
                                                     
  have hZ0 := hC0_bound δ hδ_pos
                                                                                   
  have h_tri : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤
      ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ + ‖(1 / (δ : ℂ))‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) (1 / (δ : ℂ)))
                                        
  have h_norm_div_le_two : ‖(1 / (δ : ℂ))‖ ≤ 2 := by
                                                          
    have hnorm_div : ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      simp
    have hnorm_ofReal : ‖(δ : ℂ)‖ = |δ| := by
      simp
                                        
    have h_abs_ge : (1 / 2 : ℝ) ≤ |δ| := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [abs_of_nonneg hδ_nonneg] using hδ_ge_half
    have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hone_div_abs_le_two : 1 / |δ| ≤ 2 := by
      simpa using (one_div_le_one_div_of_le hhalfpos h_abs_ge)
                                             
    have : 1 / ‖(δ : ℂ)‖ ≤ 2 := by simpa [hnorm_ofReal] using hone_div_abs_le_two
                                      
    have hnorm_div' : ‖(1 / (δ : ℂ))‖ = 1 / ‖(δ : ℂ)‖ := by
      simp
    simpa [hnorm_div'] using this
                                                                                           
  have h_real_axis_bound : ‖logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
    have h1 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + ‖(1 / (δ : ℂ))‖ :=
      le_trans h_tri (add_le_add_left hZ0 _)
    have h2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 :=
      le_trans h1 (add_le_add_right h_norm_div_le_two _)
    simpa [norm_neg] using h2
                           
  have hσ_real : (1 : ℝ) + δ = σ := by
    simp [δ, sub_eq_add_neg, add_left_comm]
  have hσ_eq : (1 : ℂ) + δ = (σ : ℂ) := by
    have : ((1 + δ : ℝ) : ℂ) = (σ : ℂ) := by simpa using congrArg Complex.ofReal hσ_real
    simpa [Complex.ofReal_add] using this
  have hR_bound : ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ C0 + 2 := by
                                                    
    simpa [logDerivZeta, hσ_eq] using h_real_axis_bound
                                    
  exact le_trans h_center hR_bound

theorem thm_final_result :
  ∃ A : ℝ, A > 0 ∧ A < 1 ∧
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 1 - A / Real.log (abs t + 2) →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C * (Real.log (abs t)) ^ 2 := by
                                                                                          
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := lem_logDerivZetalogt0
  obtain ⟨C₃₂, hC₃₂_pos, hC₃₂⟩ := lem_logDerivZetalogt32

  use zerofree_constant / 20

  constructor
  ·               
    apply div_pos zerofree_constant_pos
    norm_num

  constructor
  ·               
    rw [div_lt_one (by norm_num : (0 : ℝ) < 20)]
                                          
    have h1 : zerofree_constant < 1 := zerofree_constant_lt_one
    linarith

  use max C₀ C₃₂

  constructor
  ·               
    exact lt_max_of_lt_left hC₀_pos

  ·              
    intro t ht σ hσ

    have h_eq : zerofree_constant / 20 / Real.log (abs t + 2) = deltaz_t t := by
      unfold deltaz_t deltaz
      simp

    have hσ' : σ ≥ 1 - deltaz_t t := by
      rw [← h_eq]
      exact hσ

    by_cases h : σ ≥ 3/2
    ·                                            
      have bound := hC₃₂ t ht σ h
      have hC_le : C₃₂ ≤ max C₀ C₃₂ := le_max_right _ _
                                                      
      have hlog_ge_one : 1 ≤ Real.log (abs t) := by
        have h_ge : Real.exp 1 ≤ abs t := by
                                                     
          have he_lt_3 : Real.exp 1 < 3 := lem_three_gt_e                           
          linarith [ht, abs_nonneg t]
        exact (Real.le_log_iff_exp_le (by linarith [abs_nonneg t])).2 h_ge
      have h_one_le_sq : 1 ≤ (Real.log (abs t)) ^ 2 := by
        have h_sq : (Real.log (abs t)) ^ 2 = Real.log (abs t) * Real.log (abs t) := by
          rw [pow_two]
        rw [h_sq]
        have h_mul : 1 * 1 ≤ Real.log (abs t) * Real.log (abs t) :=
          mul_self_le_mul_self (zero_le_one) hlog_ge_one
        simpa using h_mul
      have h_pos : 0 < C₃₂ := lt_trans zero_lt_one hC₃₂_pos
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₃₂ := bound
        _ = C₃₂ * 1 := by rw [mul_one]
        _ ≤ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h_one_le_sq (le_of_lt h_pos)
        _ ≤ max C₀ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

    ·                                           
      push Not at h
      have h_conditions : 1 - deltaz_t t ≤ σ ∧ σ ≤ 3/2 ∧ t = t := by
        exact ⟨hσ', le_of_lt h, rfl⟩
      have bound := hC₀ t ht ⟨σ, t⟩ h_conditions
      have hC_le : C₀ ≤ max C₀ C₃₂ := le_max_left _ _
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₀ * Real.log |t| ^ 2 := bound
        _ ≤ max C₀ C₃₂ * Real.log |t| ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

lemma ZetaZeroFree_p :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Set.Ico (1 - A / Real.log |t| ^ 1) 1),
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
                                                                             
  obtain ⟨c, hc_pos, hc_lt_one, hbound⟩ := zerofree
                                               
  let A0 : ℝ := min (1 / 2 : ℝ) (c / 2)
  let A : ℝ := min A0 ((1 / 4 : ℝ) * Real.log 3)
  have hA_pos : 0 < A := by
    have h1 : 0 < (1 / 2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc_pos this
    have hA0pos : 0 < A0 := lt_min_iff.mpr ⟨h1, h2⟩
    have hlog3pos : 0 < Real.log (3 : ℝ) :=
      (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 3)).2 (by norm_num)
    have h3 : 0 < (1 / 4 : ℝ) * Real.log 3 := by
      exact mul_pos (by norm_num) hlog3pos
    exact lt_min_iff.mpr ⟨hA0pos, h3⟩
  have hA_le_half : A ≤ 1/2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_left _ _)
  have hA_le_c2 : A ≤ c / 2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_right _ _)
  have hA_le_log3quarter : A ≤ (1 / 4 : ℝ) * Real.log 3 := min_le_right _ _
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hA_pos, hA_le_half⟩
  · intro σ t htgt3 hσI hzero
                        
    set L := Real.log |t| with hLdef
    set Lp := Real.log (|t| + 2) with hLpdef
    have hpos_abs : 0 ≤ |t| := abs_nonneg t
    have hLpos : 0 < L := (Real.log_pos_iff hpos_abs).2 (lt_trans (by norm_num) htgt3)
    have hLp_pos_arg : 0 < |t| + 2 := by linarith
    have hLp_pos : 0 < Lp := (Real.log_pos_iff (le_of_lt hLp_pos_arg)).2 (by linarith)
                                      
    have hlog3_le_L : Real.log 3 ≤ L := by
      have h3pos : 0 < (3 : ℝ) := by norm_num
      have : (3 : ℝ) ≤ |t| := le_of_lt htgt3
      simpa [hLdef] using Real.log_le_log h3pos this
                                  
    have hquarter_ratio_le : ((1 / 4 : ℝ) * Real.log 3) / L ≤ (1 / 4 : ℝ) := by
      have h := div_le_div_of_nonneg_right hlog3_le_L (le_of_lt hLpos)
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/4)
      have hne : L ≠ 0 := ne_of_gt hLpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne] using h'
                          
    have hA_over_le_quarter : A / L ≤ (1 / 4 : ℝ) := by
      have := div_le_div_of_nonneg_right hA_le_log3quarter (le_of_lt hLpos)
      exact this.trans hquarter_ratio_le
                                   
    have hlow : 1 - A / L ≤ σ := by simpa [hLdef, pow_one] using hσI.1
    have hσ_ge_34 : (3 / 4 : ℝ) ≤ σ := by
      have : (3 / 4 : ℝ) ≤ 1 - A / L := by linarith
      exact this.trans hlow
    have hσ_pos : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3/4 : ℝ)) hσ_ge_34
    have hσ_lt_one : σ < 1 := hσI.2
                   
    have hlog_lt : Lp < 2 * L := by
      have h1 : 0 < |t| - 2 := by linarith
      have h2 : 0 < |t| + 1 := by linarith
      have hprod_pos : 0 < (|t| - 2) * (|t| + 1) := mul_pos h1 h2
      have hpoly : |t| * |t| - (|t| + 2) = (|t| - 2) * (|t| + 1) := by ring
      have hlt : |t| + 2 < |t| * |t| := by
        calc
          |t| + 2 < |t| + 2 + (|t| - 2) * (|t| + 1) := by linarith [hprod_pos]
          _ = |t| * |t| := by rw [← hpoly]; ring
      have hposb : 0 < |t| + 2 := by linarith
      have hlog_lt' : Real.log (|t| + 2) < Real.log (|t| * |t|) := Real.log_lt_log hposb hlt
      have hlogmul : Real.log (|t| ^ 2) = 2 * Real.log |t| := Real.log_pow |t| 2
      calc
        Lp = Real.log (|t| + 2) := by simp [hLpdef]
        _ < Real.log (|t| * |t|) := hlog_lt'
        _ = Real.log (|t| ^ 2) := by simp [pow_two]
        _ = 2 * Real.log |t| := by simp
        _ = 2 * L := by simp [hLdef]
                                               
    have h_inv_comp : 1 / (2 * L) < 1 / Lp := one_div_lt_one_div_of_lt hLp_pos hlog_lt
    have hstep2 : (c / 2) / L < c / Lp := by
      have hcpos' : 0 < c := hc_pos
      have : c * (1 / (2 * L)) < c * (1 / Lp) := mul_lt_mul_of_pos_left h_inv_comp hcpos'
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
                                          
    have hstep1 : A / L ≤ (c / 2) / L := by
      have := div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
      simpa [div_eq_mul_inv] using this
    have hstrict_div : A / L < c / Lp := lt_of_le_of_lt hstep1 hstep2
                                                       
    have hσ_gt : 1 - c / Lp < σ := by
      have hneg' : - (c / Lp) < - (A / L) := by simpa [neg_div] using neg_lt_neg hstrict_div
      have : 1 - c / Lp < 1 - A / L := by simpa [sub_eq_add_neg] using! add_lt_add_right hneg' 1
      exact this.trans_le hlow
                                             
    let s : ℂ := Complex.mk σ t
    have hs_zero : riemannZeta s = 0 := by simpa [s, Complex.mk_eq_add_mul_I] using hzero
    have hs_in_zeroZ : s ∈ zeroZ := by simpa [zeroZ] using hs_zero
    have hpre : s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1 := by
      refine ⟨hs_in_zeroZ, ?_, ?_⟩
      · simpa [s] using hσ_pos
      · simpa [s] using hσ_lt_one
    have him_bound : 2 < |s.im| := by
      have : 2 < |t| := lt_trans (by norm_num) htgt3
      simpa [s] using this
    have hbound_applied : s.re ≤ 1 - c / Real.log (abs s.im + 2) := hbound s hpre him_bound
    have hle : σ ≤ 1 - c / Lp := by simpa [s, hLpdef] using hbound_applied
    have hcontr : σ < σ := lt_of_le_of_lt hle hσ_gt
    exact (lt_irrefl _ : ¬ σ < σ) hcontr

open _root_.Set Function Filter _root_.Complex _root_.Real
lemma LogDerivZetaBndUnif2 :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 1)), ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      C * Real.log |t| ^ 2 := by
  classical
  obtain ⟨c, hc, hc2, K, hK, hfinal⟩ := thm_final_result
                     
  let A : ℝ := min (1/2 : ℝ) (c / 2)
  have hApos : 0 < A := by
    have h1 : 0 < (1/2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc this
    exact (lt_min_iff).2 ⟨h1, h2⟩
  have hAle : A ≤ (1/2 : ℝ) := min_le_left _ _
  have hA_in : A ∈ Ioc 0 (1/2) := ⟨hApos, hAle⟩
  let C : ℝ := K
  have hCpos : 0 < C := by
    have hKpos : 0 < K := lt_trans (by norm_num : (0 : ℝ) < 1) hK
    exact hKpos
  refine ⟨A, hA_in, C, hCpos, ?_⟩
  intro σ t htgt3 hσI
                      
  let x := |t|
  have hxpos : 0 ≤ x := abs_nonneg t
  have hxgt3 : 3 < x := htgt3
  let L := Real.log x
  let L' := Real.log (x + 2)
  have hLpos : 0 < L := (Real.log_pos_iff hxpos).2 (lt_trans (by norm_num) hxgt3)
  have hL'pos : 0 < L' :=
    (Real.log_pos_iff (by linarith : 0 ≤ x + 2)).2 (by linarith [hxpos, hxgt3])
                                             
  have hσ_ge : 1 - A / L ≤ σ := by simpa [pow_one, L, x] using hσI
                 
  have hprod_pos : 0 < (x - 2) * (x + 1) := by
    have hxgt2 : (2 : ℝ) < x := lt_trans (by norm_num) hxgt3
    exact mul_pos (sub_pos.mpr hxgt2) (add_pos_of_nonneg_of_pos hxpos (by norm_num))
  have hdiff_pos : 0 < x ^ 2 - (x + 2) := by
    have hpoly : x ^ 2 - (x + 2) = (x - 2) * (x + 1) := by ring
    simpa [hpoly] using hprod_pos
  have hlt_sq : x + 2 < x ^ 2 := by linarith
  have hlog_lt : L' < Real.log (x ^ 2) :=
    Real.log_lt_log (by linarith : 0 < x + 2) hlt_sq
  have hlog_pow : Real.log (x ^ 2) = 2 * L := by
    simp [L]
  have hL'_lt_2L : L' < 2 * L := by simpa [L', hlog_pow]
    using hlog_lt
                                       
  have hA_le_c2 : A ≤ c / 2 := min_le_right _ _
  have hstep0 : A / L ≤ (c / 2) / L :=
    div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
  have hrecip : 1 / (2 * L) < 1 / L' :=
    one_div_lt_one_div_of_lt hL'pos hL'_lt_2L
  have hmul : c * (1 / (2 * L)) < c * (1 / L') :=
    mul_lt_mul_of_pos_left hrecip hc
  have hstep2 : (c / 2) / L < c / L' := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  have hineq : A / L < c / L' := lt_of_le_of_lt hstep0 hstep2
  have hσ_gt : σ > 1 - c / L' := by
    have : 1 - c / L' < 1 - A / L := by linarith [hineq]
    exact lt_of_lt_of_le this hσ_ge
                                                 
  have hmain' : ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      K * (Real.log |t|) ^ 2 := by
    have h_eq : σ + t * Complex.I = Complex.mk σ t := by
      rw [Complex.mk_eq_add_mul_I]
    rw [h_eq]
    have hσ_ge_required : σ ≥ 1 - c / Real.log (abs t + 2) := by
      have h_abs_eq : abs t = |t| := by simp
      rw [h_abs_eq]
      exact le_of_lt hσ_gt
    exact hfinal t htgt3 σ hσ_ge_required
                                                  
  simpa [C, L, x] using hmain'

end Erdos970
