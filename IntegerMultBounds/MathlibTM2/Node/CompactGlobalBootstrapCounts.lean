module

public import IntegerMultBounds.MathlibTM2.Fast.SynRec
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Original precision/depth bootstrap. The precision source is the original unary p,
not the subsequently widened working width. Main keeps p at mnIo.dp(n) and mnRnd.pn;
the initial SynV.p.D holds original d. A caller copies those to s0/s1 before this program.
The copied source words are cleared, so s0/s1 are free for the round sources afterwards. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactOriginalGuardLog (p : ℕ) (hp : 2≤p) : synJk 2 (p-1) (p-1)=Nat.clog 2 p := by
  rw [synJk_eq_min (by decide : 1<2) (by omega)]
  have hlog := Nat.log_lt_self 2 (show p-1≠0 by omega)
  rw [min_eq_right (by omega)]
  apply eq_of_forall_lt_iff
  intro t
  rw [Nat.lt_clog_iff_pow_lt (by decide : 1<2)]
  have hh := Nat.le_log_iff_pow_le (b:=2) (x:=t) (y:=p-1) (by decide) (by omega)
  omega

/-- Preserve original precision on s0; compute guard on s19. -/
def compactGlobalGuard : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.s 0)) (sreg (.s 9)) (sreg (.s 2))) <|
  .seq (synPop (sreg (.s 9))) <|
  .seq (ucopy (sreg (.s 9)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (synCntLoop 2 (.s 9) (.s 12) (.s 10)) <|
  .seq (umul 4 (sreg (.s 12)) (sreg (.s 19)) (sreg (.s 2))) <|
  .seq (synPush (sreg (.s 19)) tick) <| .seq (synPush (sreg (.s 19)) tick) <|
  .seq (synPush (sreg (.s 19)) tick) <| .seq (synPush (sreg (.s 19)) tick) <|
  .seq (synPush (sreg (.s 19)) tick) <| .seq (synPush (sreg (.s 19)) tick) <|
  .seq (uclear (sreg (.s 9))) <| .seq (uclear (sreg (.s 10))) (uclear (sreg (.s 12)))

def compactGlobalGuardCost (p : ℕ) :=
  (4*p+4)+1+(4*(p-1)+4)+synCntCost 2 (p-1) (p-1)+
    (4*Nat.clog 2 p+4)+6+2+(2*(p-1)+2)+(2*Nat.clog 2 p+2)

theorem sg_compactGlobalGuard (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p : ℕ) (hp : 2≤p) (h0 : (v (.s 0)).length=p)
    (hz : ∀ i : Fin 32,i∈[2,9,10,12,17,19,23] → v (.s i)=[]) :
    LayRuns body compactGlobalGuard (synG R v)
      (synG R (Function.update v (.s 19) (List.replicate (4*Nat.clog 2 p+6) tick)))
      (compactGlobalGuardCost p) := by
  have h2 := hz 2 (by simp); have h9 := hz 9 (by simp)
  have h10 := hz 10 (by simp); have h12 := hz 12 (by simp)
  have h17 := hz 17 (by simp); have h19 := hz 19 (by simp); have h23 := hz 23 (by simp)
  have hj := compactOriginalGuardLog p hp
  have hdiv : (p-1)/2^(p-1)=0 := Nat.div_eq_of_lt Nat.lt_two_pow_self
  refine lr_weaken body
    ((sgU_copy body (R:=R) (v:=v) (a:=.s 0) (b:=.s 9) (t:=.s 2) (x:=p) (y:=0)
      (by decide) (by decide) (by decide) h2 h0 (by simp [h9])).seq <|
    (sgU_pop body (a:=.s 9) (y:=p) (by simp)).seq <|
    (sgU_copy body (a:=.s 9) (b:=.s 10) (t:=.s 2) (x:=p-1) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h10])).seq <|
    (sg_synCntLoop body 2 (by decide) (x:=.s 9) (cnt:=.s 12) (ctr:=.s 10) _ (p-1) (p-1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp) (by simp [h12]) (by simp) (by simp [h17]) (by simp [h2]) (by simp [h23])).seq <|
    (sgU_umul body 4 (a:=.s 12) (b:=.s 19) (t:=.s 2) (x:=Nat.clog 2 p) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hj]) (by simp [h19])).seq <|
    (sgU_push body (a:=.s 19) (y:=4*Nat.clog 2 p) (by simp)).seq <|
    (sgU_push body (a:=.s 19) (y:=4*Nat.clog 2 p+1) (by simp)).seq <|
    (sgU_push body (a:=.s 19) (y:=4*Nat.clog 2 p+2) (by simp [Nat.add_assoc])).seq <|
    (sgU_push body (a:=.s 19) (y:=4*Nat.clog 2 p+3) (by simp [Nat.add_assoc])).seq <|
    (sgU_push body (a:=.s 19) (y:=4*Nat.clog 2 p+4) (by simp [Nat.add_assoc])).seq <|
    (sgU_push body (a:=.s 19) (y:=4*Nat.clog 2 p+5) (by simp [Nat.add_assoc])).seq <|
    (sgU_clear body (a:=.s 9) (x:=0) (by simp [hdiv])).seq <|
    (sgU_clear body (a:=.s 10) (x:=p-1) (by simp)).seq <|
    sgU_clear body (a:=.s 12) (x:=Nat.clog 2 p) (by simp [hj])) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz19 : z=.s 19
    · subst z; simp [Nat.add_assoc]
    by_cases hz9 : z=.s 9
    · subst z; simp [h9]
    by_cases hz10 : z=.s 10
    · subst z; simp [h10]
    by_cases hz12 : z=.s 12
    · subst z; simp [h12]
    simp [Function.update_of_ne,hz19,hz9,hz10,hz12]
  · simp only [compactGlobalGuardCost]
    omega

def compactGlobalBootstrapCounts : Pr P (nT SXReg) Q A U :=
  .seq compactGlobalGuard <|
  .seq (ucopy (sreg (.s 1)) (sreg (.s 18)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 0))) (uclear (sreg (.s 1)))

def compactGlobalBootstrapCost (p d : ℕ) := compactGlobalGuardCost p+(4*d+4)+(2*p+2)+(2*d+2)

theorem sg_compactGlobalBootstrapCounts (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p d : ℕ) (hp : 2≤p) (h0 : (v (.s 0)).length=p) (h1 : (v (.s 1)).length=d)
    (hz : ∀ i : Fin 32,i∈[2,9,10,12,17,18,19,23] → v (.s i)=[]) :
    LayRuns body compactGlobalBootstrapCounts (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v
        (.s 19) (List.replicate (4*Nat.clog 2 p+6) tick)) (.s 18) (List.replicate d tick))
        (.s 0) []) (.s 1) [])) (compactGlobalBootstrapCost p d) := by
  have hguard := sg_compactGlobalGuard body R v p hp h0 (fun i hi => hz i (by simp only [List.mem_cons] at hi ⊢; tauto))
  have h2 := hz 2 (by simp); have h18 := hz 18 (by simp)
  exact lr_weaken body (hguard.seq <|
    (sgU_copy body (a:=.s 1) (b:=.s 18) (t:=.s 2) (x:=d) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [h1]) (by simp [h18])).seq <|
    (sgU_clear body (a:=.s 0) (x:=p) (by simp [h0])).seq <|
    sgU_clear body (a:=.s 1) (x:=d) (by simp [h1])) rfl (by simp only [compactGlobalBootstrapCost]; omega)

end
end IntegerMultBounds.MathlibTM2.Fast
