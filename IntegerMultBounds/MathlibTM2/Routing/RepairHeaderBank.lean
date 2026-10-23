module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderBank
public import IntegerMultBounds.MathlibTM2.Routing.RoutingHeaderCopy
public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBank

/-! The ten canonical headers for the two R2 interchange banks.
Each destination is the actual raw configuration register used by repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairHeaderIndex (j : Fin 10) : Fin 2 × Fin 5 :=
  (⟨j.val / 5, by have := j.isLt; omega⟩, ⟨j.val % 5, Nat.mod_lt _ (by decide)⟩)

theorem repairHeaderIndex_injective : Function.Injective repairHeaderIndex := by
  intro j k he
  have hc := congrArg (fun x : Fin 2 × Fin 5 => x.1.val) he
  have hk := congrArg (fun x : Fin 2 × Fin 5 => x.2.val) he
  apply Fin.ext
  dsimp [repairHeaderIndex] at hc hk
  omega

def repairHeaderDestination (j : Fin 10) : Fin repairT :=
  repairRoutingConfig (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)

theorem repairHeaderDestination_injective : Function.Injective repairHeaderDestination := by
  intro j k he
  apply repairHeaderIndex_injective
  simp only [repairHeaderDestination, repairRoutingConfig, placedSelectiveConfig,
    repairRoutingEmbed_reg, repairRoutingRole, repairReg_inj, RepairReg.routing.injEq, SelectiveReg.config.injEq, SetupKey.header.injEq] at he
  exact Prod.ext he.1 he.2

def repairHeaderValue (p : Par) (X rb R B : ℕ) (j : Fin 10) : ℕ :=
  selectiveSwapValues p X R (fieldsLen (selectiveKeyLen p X rb) + B) (repairHeaderIndex j).1 (repairHeaderIndex j).2

def repairHeaderJobs (p : Par) (X rb R B : ℕ) (L : Fin 10 → ℕ) :=
  List.ofFn (headerBankJob repairHeaderDestination L (repairHeaderValue p X rb R B))

theorem repairHeaderBank_contents {A : ℕ} (p : Par) (X rb R B : ℕ) (L : Fin 10 → ℕ)
    (bank : Fin (repairT + (10 + 2)) → List (Fin (A + 4))) (j : Fin 10) :
    canonicalHeadersGenerated bank (repairHeaderJobs p X rb R B L) (headerCore (repairHeaderDestination j)) =
      (repairCanonicalHeaders p X rb R B (repairHeaderIndex j).1 (repairHeaderIndex j).2).map bitSymbol := by
  exact headerBank_contents repairHeaderDestination repairHeaderDestination_injective L (repairHeaderValue p X rb R B) bank j

theorem repairHeaderBank_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P (repairT + (10 + 2)) Q A U) (p : Par) (X rb R B : ℕ) (L : Fin 10 → ℕ)
    (v : HS (repairT + (10 + 2)) Q A U) (S : Stacks (repairT + (10 + 2)) A)
    (hfit : ∀ j, repairHeaderValue p X rb R B j < 2 ^ L j)
    (hsource : ∀ j, S.R (headerAux ⟨j.val, by omega⟩) = binSyms (L j) (repairHeaderValue p X rb R B j))
    (hblank : ∀ j, S.R (headerCore (repairHeaderDestination j)) = [])
    (htmp : S.R (headerAux 10) = []) (hwork : S.R (headerAux 11) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (canonicalHeaderBatch (repairHeaderJobs p X rb R B L)) (mk v S)
        (canonicalHeaderBatchCost (repairHeaderJobs p X rb R B L))
        (mk v' { S with R := canonicalHeadersGenerated S.R (repairHeaderJobs p X rb R B L) }) := by
  exact headerBank_exec body repairHeaderDestination repairHeaderDestination_injective L (repairHeaderValue p X rb R B)
    v S hfit hsource hblank htmp hwork

end
end IntegerMultBounds.MathlibTM2.Routing
