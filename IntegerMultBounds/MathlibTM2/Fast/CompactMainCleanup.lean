module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransport
public import IntegerMultBounds.MathlibTM2.Fast.MainPush

/-! Complete expanded-register cleanup and restoration of the initial local state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
noncomputable section
variable {A : ℕ}

/-- Empty every register, including the compact private bank. -/
def compactMainClear : CompactMnPr CompactMainProc A :=
  Prog.seqList ((List.finRange compactMnT).map emptyR)

def compactMainV₀ : HS compactMnT compactMnQ A Unit :=
  ⟨false,none,⟨0,compactMnQ_pos⟩,fun _ => blank,none,()⟩

def compactMainReset : CompactMnPr CompactMainProc A :=
  .act (.load (fun _ => compactMainV₀) .done)

def compactMainIn (l : List (Bool ⊕ Bool)) : Stacks compactMnT A :=
  ⟨l,[],fun _ => [],fun _ => []⟩

lemma compactMain_only_inp (v : HS compactMnT compactMnQ A Unit) (l : List (Bool ⊕ Bool)) :
    (Store.only v .inp l : Store (HΓ (T := compactMnT) A) (HS compactMnT compactMnQ A Unit)) =
      mk v (compactMainIn l) := by
  refine Store.ext rfl (funext fun k => ?_)
  cases k <;> rfl

lemma compactMainIn_projection (l : List (Bool ⊕ Bool)) :
    embStk compactMnLegacyReg (compactMainIn (A := A) l)=⟨l,[],fun _ => [],fun _ => []⟩ := rfl

private lemma zeroDown {Q Q' : ℕ} (hQ : 0<Q) (hQ' : 0<Q') :
    stateLiftFinDown hQ (⟨0,hQ'⟩ : Fin Q')=⟨0,hQ⟩ := by
  unfold stateLiftFinDown
  exact dite_eq_left hQ

lemma compactMainV₀_projection : compactMainStateDown (compactMainV₀ (A := A))=mnV₀ := by
  simp only [compactMainStateDown,compactMainV₀,mnV₀,embDn,stateLiftDown,
    zeroDown,Option.map_none,Function.comp_def]

/-- Exact cleanup cost on the expanded host. -/
theorem compactMainClear_exec (body : CompactMainProc → CompactMnPr CompactMainProc A)
    (v : HS compactMnT compactMnQ A Unit) (S : Stacks compactMnT A) :
    ∃ v',Exec body compactMainClear (mk v S)
      (2*∑ i,(S.R i).length+2*compactMnT+1) (mk v' {S with R := fun _ => []}) := by
  unfold compactMainClear
  with_reducible exact (mn_clearAll_exec body v S)

theorem compactMainReset_exec (body : CompactMainProc → CompactMnPr CompactMainProc A)
    (v : HS compactMnT compactMnQ A Unit) (S : Stacks compactMnT A) :
    Exec body compactMainReset (mk v S) 1 (mk compactMainV₀ S) :=
  Exec.act (body := body) _ (mk v S)

private theorem finish {T Q A : ℕ} {P U : Type} (v₀ : HS T Q A U)
    {c : ℕ} (body : P → Pr P T Q A U) (hb : ∀ f,mnProgPush (body f)≤c)
    (p : Pr P T Q A U) (hp : mnProgPush p≤c) (l : List (Bool ⊕ Bool)) (o : List Bool)
    {m : ℕ} {v : HS T Q A U} {S : Stacks T A}
    (e : Exec body p (Store.only v₀ .inp l) m (mk v S))
    (hinp : S.inp=[]) (hout : S.out=o) (hL : ∀ k,S.L k=[]) :
    ∃ m',m'≤m+2*(l.length+c*m)+2*T+2 ∧
      Exec body (.seq p (.seq (Prog.seqList ((List.finRange T).map emptyR))
        (.act (.load (fun _ => v₀) .done)))) (Store.only v₀ .inp l) m' (Store.only v₀ .out o) := by
  obtain ⟨w,hclear⟩ := mn_clearAll_exec body v S
  have hreset : Exec body (.act (.load (fun _ => v₀) .done))
      (mk w {S with R := fun _ => []}) 1 (mk v₀ {S with R := fun _ => []}) := Exec.act _ _
  have hz := mn_exec_size e hp hb
  have hs : mnSize (Store.only (Γ := HΓ A) v₀ (HK.inp : HK T) l)=l.length := by
    unfold mnSize
    rw [Finset.sum_eq_single HK.inp]
    · rfl
    · intro k _ hk
      cases k with
      | inp => exact absurd rfl hk
      | _ => rfl
    · simp
  rw [hs] at hz
  have hR := (mn_sumR_le_size v S).trans hz
  have hfin : mk v₀ {S with R := fun _ => []}=Store.only v₀ .out o := by
    refine Store.ext rfl (funext fun k => ?_)
    cases k with
    | inp => exact hinp
    | out => exact hout
    | lt i => exact hL i
    | rt i => rfl
  refine ⟨m+(2*∑ i,(S.R i).length+2*T+1+1),by omega,?_⟩
  rw [←hfin]
  exact e.seq (hclear.seq hreset)

/-- A correct prefix yields a clean final output with the expanded cleanup overhead. -/
theorem compactMain_finish {c : ℕ} (body : CompactMainProc → CompactMnPr CompactMainProc A)
    (hb : ∀ f,mnProgPush (body f)≤c) (p : CompactMnPr CompactMainProc A)
    (hp : mnProgPush p≤c) (l : List (Bool ⊕ Bool)) (o : List Bool)
    {m : ℕ} {v : HS compactMnT compactMnQ A Unit} {S : Stacks compactMnT A}
    (e : Exec body p (Store.only compactMainV₀ .inp l) m (mk v S))
    (hinp : S.inp=[]) (hout : S.out=o) (hL : ∀ k,S.L k=[]) :
    ∃ m',m'≤m+2*(l.length+c*m)+2*compactMnT+2 ∧
      Exec body (.seq p (.seq compactMainClear compactMainReset))
        (Store.only compactMainV₀ .inp l) m' (Store.only compactMainV₀ .out o) := by
  unfold compactMainClear compactMainReset
  with_reducible exact (finish compactMainV₀ body hb p hp l o e hinp hout hL)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
