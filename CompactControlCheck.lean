module

import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedReservationGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTopGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTopCost
import IntegerMultBounds.MathlibTM2.Fast.CompactParamProg
import IntegerMultBounds.MathlibTM2.Fast.CompactParamPipeline
import IntegerMultBounds.MathlibTM2.Fast.CompactDistRetune
import IntegerMultBounds.MathlibTM2.Fast.CompactDist
import IntegerMultBounds.MathlibTM2.Fast.CompactDistWires
import IntegerMultBounds.MathlibTM2.Fast.CompactDistWiresExec
import IntegerMultBounds.MathlibTM2.Fast.CompactBundleMnLay
import IntegerMultBounds.MathlibTM2.Fast.CompactSynMainFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcMachine
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcBase
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcStages
import IntegerMultBounds.MathlibTM2.Fast.CompactSynMainEntry
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcMainStages
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUniformExecution
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUniformStream
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformHybridRound
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLayerContract
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformRound
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopCost
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopFStep
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopOStep
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopF
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopO
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLoopsContract
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformFwd
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformOpp
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformTransformPre
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformFwdSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformOppSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformTransforms
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedGeometry
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransforms
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerCombinedBudget
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformReadiness
import IntegerMultBounds.MathlibTM2.Cost.CompactPieceUniformPacking
import IntegerMultBounds.MathlibTM2.Fast.CompactTopUniformRuntimeExecution
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUniformRuntime
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerGuardPower
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerLayerGrowth
import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwd
import IntegerMultBounds.MathlibTM2.Fast.CompactSynOpp
import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre
import IntegerMultBounds.MathlibTM2.Fast.CompactSynFwdSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynOppSpec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialTransforms
import IntegerMultBounds.MathlibTM2.Fast.CompactSynConcreteTransforms
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerDivisorPolynomial
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRetunedCapacity
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerScalarBudget
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformRuntime
import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerContract
import IntegerMultBounds.MathlibTM2.Fast.CompactSynTwiddle
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRound
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopBody
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopCost
import IntegerMultBounds.MathlibTM2.Fast.CompactSynScanFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopFStep
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopOStep
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopF
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopO
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopsContract
import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialGeometry
import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialContract
import IntegerMultBounds.MathlibTM2.Fast.CompactSynInitialLoops
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayoutTransport
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapView
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapTransformFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransformPipeline
import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadRuntime
import IntegerMultBounds.MathlibTM2.Cost.CompactRuntimePolynomial
import IntegerMultBounds.MathlibTM2.Cost.CompactRoundVolume
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerFullDimension
import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadBound
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineCompose
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelinePrecision
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapRuntime
import IntegerMultBounds.MathlibTM2.Fast.CompactSynHybridRound
import IntegerMultBounds.MathlibTM2.Fast.CompactMainLayer
import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalCompleteBound
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepStream
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransport
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepExecution
import IntegerMultBounds.MathlibTM2.Cost.CompactTopRecordSetupBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalRuntime
import IntegerMultBounds.MathlibTM2.Cost.CompactTopCompleteBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalGeometry
import IntegerMultBounds.MathlibTM2.Host.StateLift
import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlPower
import IntegerMultBounds.MathlibTM2.Cost.CompactTopCoordinates
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPrepare
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepBasis
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPark
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCleanup
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepClear
import IntegerMultBounds.MathlibTM2.Cost.CompactTopPieceCount
import IntegerMultBounds.MathlibTM2.Fast.CompactMainConstants
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepSeq
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepProjection
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepWires
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRecords
import IntegerMultBounds.MathlibTM2.Cost.CompactTopRecordBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopBlockBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopOverhead
import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlVolume
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrap
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepSources
import IntegerMultBounds.MathlibTM2.Fast.CompactMainRegs
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundGlobal
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundRegs
import IntegerMultBounds.MathlibTM2.Node.CompactGlobalBootstrap
import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshRest
import IntegerMultBounds.MathlibTM2.Cost.CompactTopRowControlBound
import IntegerMultBounds.MathlibTM2.Cost.CompactInterimParameters
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest
import IntegerMultBounds.MathlibTM2.Node.CompactBasisCleanup
import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefresh
import IntegerMultBounds.MathlibTM2.Node.CompactGlobalBootstrapCounts
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundRest
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundPark
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundCompose
import IntegerMultBounds.MathlibTM2.Fast.CompactTopRuntimeExecution
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundSources
import IntegerMultBounds.MathlibTM2.Cost.CompactTopControlBound
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetup
import IntegerMultBounds.MathlibTM2.Cost.CompactTopBound
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerShape
import IntegerMultBounds.MathlibTM2.Cost.CompactLayerBound
import IntegerMultBounds.MathlibTM2.Fast.CompactPieceGeometry
import IntegerMultBounds.MathlibTM2.Fast.CompactTopExecution
import IntegerMultBounds.MathlibTM2.Cost.CompactPiecePacking
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupCounts
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupPlacement
import IntegerMultBounds.MathlibTM2.Cost.CompactLayerNormalized
import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
import IntegerMultBounds.MathlibTM2.Node.CompactTopProc
import IntegerMultBounds.MathlibTM2.Cost.CompactLayerReady
import IntegerMultBounds.MathlibTM2.Fast.CompactTopPrecision
import IntegerMultBounds.MathlibTM2.Node.CompactLayerGeometry
import IntegerMultBounds.MathlibTM2.Node.CompactTopProcLeaf
import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced
import IntegerMultBounds.MathlibTM2.Cost.CompactFactorActual
import IntegerMultBounds.MathlibTM2.Cost.CompactBasis
import IntegerMultBounds.MathlibTM2.Node.CompactFactor
import IntegerMultBounds.MathlibTM2.Fast.CompactTopOriginal
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows
import IntegerMultBounds.MathlibTM2.Node.CompactBasisRegisters
import IntegerMultBounds.MathlibTM2.Fast.CompactTopSetup
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerCapacity
import IntegerMultBounds.MathlibTM2.Node.CompactBasis
import IntegerMultBounds.MathlibTM2.Fast.CompactTopReady
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRows
import IntegerMultBounds.MathlibTM2.Node.CompactSlotComputed
import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfig
import IntegerMultBounds.MathlibTM2.Cost.CompactSwap
import IntegerMultBounds.MathlibTM2.Node.CompactRotParity
import IntegerMultBounds.MathlibTM2.Cost.CompactStageExec
import IntegerMultBounds.MathlibTM2.Node.CompactGeometry
import IntegerMultBounds.MathlibTM2.Cost.CompactRuntime
import IntegerMultBounds.MathlibTM2.Cost.CompactParameters
import IntegerMultBounds.MathlibTM2.Node.CompactRotRuntime
import IntegerMultBounds.MathlibTM2.Node.CompactGeometryRecursive
import IntegerMultBounds.MathlibTM2.Node.CompactEncoding
import IntegerMultBounds.MathlibTM2.Node.CompactSlotXor
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecArithmetic
import IntegerMultBounds.MathlibTM2.Cost.CompactSlotXor
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecPieces
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRec
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecRows
import IntegerMultBounds.MathlibTM2.Fast.CompactSynSel
import IntegerMultBounds.MathlibTM2.Node.CompactEncodingOffset
import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry
import IntegerMultBounds.MathlibTM2.Fast.CompactSynCoverage
import IntegerMultBounds.MathlibTM2.Node.CompactHeaderBuild
import IntegerMultBounds.MathlibTM2.Node.CompactHeaderBank
import IntegerMultBounds.MathlibTM2.Node.CompactHeaderClear
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRows
import IntegerMultBounds.MathlibTM2.Node.CompactSlotPrepared
import IntegerMultBounds.MathlibTM2.Cost.CompactPrepared
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecRoot
import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorArithmetic
import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorPadding
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerParameters
import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorBankOps
import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorBank
import Lean.Util.CollectAxioms
import IntegerMultBounds.MathlibTM2.Cost.CompactGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactStageGrowth
import IntegerMultBounds.MathlibTM2.Cost.CompactTotal
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerSlack
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerTopCost
import IntegerMultBounds.MathlibTM2.Fast.CompactBdRetune
import IntegerMultBounds.MathlibTM2.Fast.CompactBdWiresCost
import IntegerMultBounds.MathlibTM2.Fast.CompactBundleWires
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedMainFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedMainEntry
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedDistributionEntry
import IntegerMultBounds.MathlibTM2.Fast.CompactMainCalls
import IntegerMultBounds.MathlibTM2.Fast.CompactMainEntryTable
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedDirectCost
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransformCalls
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedEntrySpecs
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcRetunedFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSrcRetunedStages
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeGlue
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeBound
import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrimitiveRuns
import IntegerMultBounds.MathlibTM2.Fast.CompactSynDispatch
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLoopMatch
import IntegerMultBounds.MathlibTM2.Fast.CompactSourceCost
import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsCost
import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsTime
import IntegerMultBounds.MathlibTM2.Fast.CompactMainStableFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactMainSourceLift
import IntegerMultBounds.MathlibTM2.Fast.CompactMainSourceStages
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedLayoutMatch
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedStashMatch
import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipeline
import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrimitiveEntry
import IntegerMultBounds.MathlibTM2.Fast.CompactMainDispatch
import IntegerMultBounds.MathlibTM2.Fast.CompactRetunedMainBound
import IntegerMultBounds.MathlibTM2.Fast.CompactMainChain
import IntegerMultBounds.MathlibTM2.Fast.CompactMainParamCalls
import IntegerMultBounds.MathlibTM2.Fast.CompactMainCleanup
import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsAt
import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainExec
import IntegerMultBounds.MathlibTM2.Fast.CompactMainChainEntry
import IntegerMultBounds.MathlibTM2.Fast.CompactMainCoefficients
import IntegerMultBounds.MathlibTM2.Fast.CompactMainHost
import IntegerMultBounds.MathlibTM2.Fast.CompactMainPrefixCost
import IntegerMultBounds.MathlibTM2.Fast.CompactMainDistributionCalls
import IntegerMultBounds.MathlibTM2.Fast.CompactMainInputDistribution
import IntegerMultBounds.MathlibTM2.Fast.CompactMainOutput
import IntegerMultBounds.MathlibTM2.Fast.CompactFinal
import IntegerMultBounds.MathlibTM2.Cost.CompactDimensionParameters
import IntegerMultBounds.MathlibTM2.Cost.CompactTopAbsoluteBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopActualBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalBound
import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalVolume
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineGlobals
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineSource
import IntegerMultBounds.MathlibTM2.Fast.CompactMainLegacyRuns
import IntegerMultBounds.MathlibTM2.Fast.CompactSynDirect
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepAlgebra
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCompose
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepReady
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRefresh
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRuntime
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepSemantics
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUnpark
import IntegerMultBounds.MathlibTM2.Fast.CompactSynMainProjection
import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshInput

/-! Focused integrity audit for the compact-control host primitives.
These are prepared execution contracts, not an improved layer or multiplier theorem. -/

open Lean in
run_cmd do
  let names := #[
    ``IntegerMultBounds.MathlibTM2.Node.compactSwap_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactParityPack_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactParityWord_binSyms,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSwapCost_le_volume,
    ``IntegerMultBounds.MathlibTM2.Node.compactNativeProg_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactEarlyProg_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactLateProg_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactStageWords_length_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactStageBankSize_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactEarlyProg_exec_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLateProg_exec_le,
    ``IntegerMultBounds.MathlibTM2.Node.compactNative_destination_rank,
    ``IntegerMultBounds.MathlibTM2.Node.compactNative_result_entry,
    ``IntegerMultBounds.MathlibTM2.Node.compactRuntimeProg_exec,
    ``IntegerMultBounds.MathlibTM2.Node.CompactRecursiveLayout.child,
    ``IntegerMultBounds.MathlibTM2.Node.compactRecursiveNative_serialized_rank,
    ``IntegerMultBounds.MathlibTM2.Node.compactEncoding_exists,
    ``IntegerMultBounds.MathlibTM2.Node.compactEncoding_runtime_result,
    ``IntegerMultBounds.MathlibTM2.Node.compactSlotXor_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntimeProg_exec_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntimePacked_of_dyadic,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactCeil,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactReserveCounts,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSlotXorCost_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSlotXor_exec_le,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactReservedPieces,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactSynRec,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactRowReserve,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservedPcs_ok,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservedPcs_exp_sum,
    ``IntegerMultBounds.MathlibTM2.Node.compactOffsetArray_encZ,
    ``IntegerMultBounds.MathlibTM2.Node.compactOffsetArray_encZ_pullM,
    ``IntegerMultBounds.MathlibTM2.Node.compactOffset_volume,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservation_bits,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservationChildLayout,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservationDigitLayout,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservation_volume,
    ``IntegerMultBounds.MathlibTM2.Fast.compactReservation_full_coverage,
    ``IntegerMultBounds.MathlibTM2.Node.compactHeadersBuild_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactHeaderFill_native,
    ``IntegerMultBounds.MathlibTM2.Node.compactHeadersClear_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.compactRebasePc_record,
    ``IntegerMultBounds.MathlibTM2.Fast.compactRebasedPcs_initial_ok,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSyn_depth_le,
    ``IntegerMultBounds.MathlibTM2.Node.compactSlotPrepared_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSlotPreparedCost_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSlotPrepared_exec_le,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactSynRoot,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopRows_bounds,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopRows_pcs_ok,
    ``IntegerMultBounds.MathlibTM2.Node.compactDescriptorQuotient_runs,
    ``IntegerMultBounds.MathlibTM2.Node.compactDescriptorStage_runs,
    ``IntegerMultBounds.MathlibTM2.Node.compactDescriptorStage_exact,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopKernel_fits,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopSelection_vals,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSelection_nodup,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPcs_ok,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPcs_exp,
    ``IntegerMultBounds.MathlibTM2.Node.compactDescriptorBank_runs,
    ``IntegerMultBounds.MathlibTM2.Node.compactDescriptorBank_original_lengths,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Node.compactSlotComputed_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactTopConfig,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_topRows_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_topRows_quotient_le,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSelection_mem,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSelection_length,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTop_shift,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTop_working_pcs_ok,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPieces_injective,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopZ_correct,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_guardLog,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_guard,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_fits_iff,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_reservation,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_capacity,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_synDp,
    ``IntegerMultBounds.MathlibTM2.Node.compactBasisSlot_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactBasisList_exec,
    ``IntegerMultBounds.MathlibTM2.Node.compactBasis_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactTopCoordinates,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactTopSetup,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactTopRecordSetup,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisW_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactTopOriginal,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_selected_split,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_selected_native_rows,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_selected_rows_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_selected_extra_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_selected_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactDescriptorBank_actual_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactBasisSlotCost_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactBasisCost_le,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisW_factor_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactFactorProg_spec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLayer_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLayer_callSpec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLayerReady_of_layout,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopRd_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopCallClr_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopKerS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopLeafKerS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisTopLeaf_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLegacyReg_injective,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLayerReg_injective,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLegacyReg_ne_compact_bc,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactLayerReg_ne_legacy_bc,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPlaced_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.compactFactorCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactFactorCost_le,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactPlacedLayer_callSpec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopDownS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopUpS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopPadS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopUnpadS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopPcBody_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopPcLoop_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopBlockS_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopProg_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactTopProg_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerBasisBudget_covers,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerCost_compact_majorant,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerReady_canonical,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPre_fits,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopInput_fits,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerNormalized_succ,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerNormalized_zero,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerBasisBound_ratio,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPcs_offset,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopPcs_layout,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopKernel_geometry,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopActual_callSpec,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopActual_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerNormalized_closed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayerCost_closed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactLayer_br_logb,
    ``IntegerMultBounds.MathlibTM2.Cost.compactPiece_descendant_rows,
    ``IntegerMultBounds.MathlibTM2.Cost.compactPiece_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactPiece_eventually_ready,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactBasisCounts,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_shape,
    ``IntegerMultBounds.MathlibTM2.Cost.compactDigit_envelope,
    ``IntegerMultBounds.MathlibTM2.Cost.compactGeometric_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactDigit_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSynPcs_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSynDigits_support,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSynPcs_envelope_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPcsCost_split,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopCost_split,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisSetup_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPhaseSCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopUnitSCost_linear,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopRuntime_eventually_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactSynChunkSource,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynChunkSourcePlaced_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopWidenSCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopShiftWordCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopShiftSCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopDownCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopUpCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPadCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopUnpadCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactInterim.compact_slacks,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactInterim.margin_covers,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisSetup_actual_rest,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisCleanup_runs,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisRefresh_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisRefreshCleanup_runs,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisRefresh_preserves_global,
    ``IntegerMultBounds.MathlibTM2.Fast.sg_compactGlobalBootstrapCounts,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynRestUp_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynRestDown_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynStash_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynUnstash_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynPushCfg_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynDropCfg_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.CompactPlacedRuns.seq,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnLegacyReg_injective,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnLayerReg_injective,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMn_stream_shared,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnLegacyReg_ne_private,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMn_precision_source,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynGlobalRead_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynRest_of_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynTopRegs_of_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynTopIn_of_legacy,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactGlobalBootstrap_exec,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactGlobalBootstrap_initialized,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisRefresh_actual_rest,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPc_header_bounds,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPcCost_control,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPcsCost_control,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPcRecLen_control,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopBlockCost_control,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopControlCost_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopControlCost_volume,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrapRead_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.CompactPlacedRuns.layRuns,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynOutsideRowPush_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynSourceClear_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerSources_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerStep,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPcs_length_log,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnQ_pos,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnQ_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnQ_runtime,
    ``IntegerMultBounds.MathlibTM2.Fast.LayRuns.compact_seq_assoc,
    ``IntegerMultBounds.MathlibTM2.Fast.LayRuns.compact_seq_assoc_rev,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerSourcesOut_projection,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerSourcesOut_compact,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynRaised_prepared,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynRaised_prepared_synXS,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynParkedW_empty,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynRaised_restore,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerRecords_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopPcs_length_power,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopControlCost_power,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRelativePc_rebase,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRelativePc_synPcs,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRelativePc_reserved,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRelativePc_ok,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRelative_volume,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_copies_cleared,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_frame,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_preserves_precision,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_preserves_depth,
    ``IntegerMultBounds.MathlibTM2.LayerMachine.compactBasisRefresh_input,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerRefresh_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerRefresh_projection,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerRecordsRefresh_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerPrepare_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerPrepare_basis,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerPark_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerCleanup_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerClear_projection,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopCallCost_eq_piece,
    ``IntegerMultBounds.MathlibTM2.Cost.compactActiveCost_sum_with,
    ``IntegerMultBounds.MathlibTM2.Cost.compactReservedCost_sum_with,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopCallCost_reserved_sum,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopCallCost_kernel,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopCost_complete,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopConfigFieldsCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopConfigWriteCost_linear,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopConfigPaddingCost_bound,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopConfigRowsAfterCost_bound,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopOriginalAdapterCost_bound,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopConfigRowsCost_volume,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopOriginalAdapterCost_volume,
    ``IntegerMultBounds.MathlibTM2.Cost.compactUnaryPaddingBudget_volume,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopOriginal_division_volume,
    ``IntegerMultBounds.MathlibTM2.Host.stateMapAct_run,
    ``IntegerMultBounds.MathlibTM2.Host.stateMap_exec,
    ``IntegerMultBounds.MathlibTM2.Host.stateMap_exec_normalized,
    ``IntegerMultBounds.MathlibTM2.Host.stateLiftDown_up,
    ``IntegerMultBounds.MathlibTM2.Host.stateLift_exec,
    ``IntegerMultBounds.MathlibTM2.Host.stateLift_exec_normalized,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerPrepare_projection,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynParkedFile_topRegs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynParkedFile_topIn,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynParkedRuntime_eventually_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerUnpark_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerStep_compose,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayer_final_background,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerStep_eventually_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRowReserveCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCeilCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactReserveCountsCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactBackPieceCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopCoordinatesCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactReservedPiecesCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopRecordSetupCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopConfigDivisorCost_poly,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_row_room,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopOriginal_runtime_eventually_division,
    ``IntegerMultBounds.MathlibTM2.Host.statePlaced_exec,
    ``IntegerMultBounds.MathlibTM2.Host.statePlaced_exec_normalized,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainTransport_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStage_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainFinalStacks_projection,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainFinalStacks_io,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainFinalStacks_private,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopOriginalCost_complete,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynSelection_physical,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynSelection_stream,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerStep_eventually_exec_stream,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainBody_layer,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainLayer_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainLayer_io_restore,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainChunk_runs,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntime_eventually_polynomial,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntime_eventually_scalar_power,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRuntime_eventually_setup_volume,
    ``IntegerMultBounds.MathlibTM2.Cost.compactTopWorkingVolume_bounds,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_chunk_predecessor,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_full_dimension,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_eventually_initial_synDp,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSynLayerRoundOverhead_complete,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynCompare_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_original_depth_file,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainGlobals_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnOriginalBootstrap_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_globals,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrapCleanup_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnGlobalsExit_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_initial_depth,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_distribution_depth,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_placed_depth,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnTransformPipeline_sources_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_parameter_precision,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrap_placed_precision,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainGlobals_runtime_words,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainGlobals_runtime_lengths,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_io_private,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainGlobals_io_update,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStage_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactOldLayer_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactLegacyLayer_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynDispatchWith_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactLegacyLayer_io_restore,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainDirect_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnLayerReg_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynDispatch_eventually_exec_stream,
    ``IntegerMultBounds.MathlibTM2.Cost.compactSynLayerRoundOverhead_eventually,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_divisor_polynomial,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_runtime_divisor_polynomial,
    ``IntegerMultBounds.MathlibTM2.Cost.compactReservationFits_mono_chunk,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_retuned_eventually_full_dimension,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_uniform_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Mult.CompactSizes.d_le_two_Kroot,
    ``IntegerMultBounds.MathlibTM2.Mult.CompactSizes.K_le_two_Kroot,
    ``IntegerMultBounds.MathlibTM2.Mult.CompactSizes.mod_K_succ_le,
    ``IntegerMultBounds.MathlibTM2.Mult.CompactSizes.old_K_le_K,
    ``IntegerMultBounds.MathlibTM2.Mult.CompactSizes.eventually_guard_room,
    ``IntegerMultBounds.MathlibTM2.Mult.CompactSizes.eventually_K_le_predecessor,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRoundF_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRoundO_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynLoopF_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynLoopO_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynLoopsContract_of_layer,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynInitialGeometry_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynInitialContract_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynInitialLoops_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnOriginalBootstrap_from_sources,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrapFinal_globalsOnly,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrapFinal_view,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnBootstrapFinal_ready,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnGlobalsExit_after_transform,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnTransformPipeline_from_sources,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_uniform_eventually_shape,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_uniform_selected_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_retuned_eventually_shape,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_retuned_selected_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactPiece_uniform_eventually_packed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactPiece_uniform_eventually_ready,
    ``IntegerMultBounds.MathlibTM2.Fast.compactTopRuntime_uniform_eventually_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynParkedRuntime_uniform_eventually_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_guard_log,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_guard_power,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_layer_guard_absorbed,
    ``IntegerMultBounds.MathlibTM2.Cost.compactCaller_interim_layer_growth,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynFwdCore_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynOppCore_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynFwd_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynOpp_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynInitialFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynInitialOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynConcreteFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynConcreteOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_chunk_lower,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_reservation_power,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_top_envelope,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_top_cost,
    ``IntegerMultBounds.MathlibTM2.Mult.Sizes.epsilon_eq,
    ``IntegerMultBounds.MathlibTM2.Mult.Sizes.d_pow_le,
    ``IntegerMultBounds.MathlibTM2.Mult.Sizes.d_eq_floor,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactDyadicParamStage_do,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactDyadicParamAtoms_le,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.pm_prelude_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.pmParams_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactPmOverwrite_do,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactPmVals_chunk,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactPmVals_other,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactPmStages_do,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactPmCode1_do,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactPmOverwriteAtoms_le,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactDsRetune_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.TableVM.compactDsIoAll_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactDsyV₀_wires,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactDs_layHyp,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactDsyWires_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynMainPre_entry,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynMainFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynMainOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMnT_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynView_source_frame,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynPre_source_framed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcBase_of_legacy,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynMainPre_placed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynPre_placed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcMainFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcMainOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerStep_uniform_eventually_exec_Hl,
    ``IntegerMultBounds.MathlibTM2.Fast.compactSynLayerStep_uniform_eventually_exec_stream,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynDispatch_uniform_eventually_exec_stream,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLayerContract_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformRoundF_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformRoundO_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLayerCost_mono,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformRoundFCost_mono,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformRoundOCost_mono,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLoopF_step,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLoopO_step,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLoopF_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLoopO_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLoopsContract_of_layer,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformLoopsContract_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformFwdCore_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformFwdCore_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformOppCore_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformOppCore_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformView_scratch,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformFwd_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformOpp_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynUniformOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedGeometry_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.compact_rpow_le_four_K_rpow,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.exp_facts,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.mp_le,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.resamp_le,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.conv_inner_nonneg,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.conv_le,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.conv_nonneg,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.regime,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.bound_le,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.bound_isBigO,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactTotal.htime,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_caller_eventually_slack,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_caller_guard,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_caller_top_cost,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactBdRetuneFile_off,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactBdRetuneFile_pre,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactBdRetune_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactBdWires_spec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactDsyWiresCost_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactDsRetuneCost_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactBdWiresCost_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactDsy_initial_depth,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedMainPre_entry,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedMainFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedMainOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedMainPre_placed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedPre_placed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedMainPre_of_distribution,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactBdDist_entry_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.exec_of_callsWithin,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.callsWithin_embProg,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.callsWithin_embProg_iff,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.callsWithin_stateLiftPr_iff,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainBody_layers_closed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainEntry_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_inst,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_direct_w2_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_tw_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_conv_ge,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_direct_over_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_direct_layer_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainBootstrap_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStage_layer_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainDispatch_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainLoopF_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainLoopO_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainFwd_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainOpp_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedFwd_entry_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynRetunedOpp_entry_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSynPre_source_framed_of,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcRetunedFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSrcRetunedOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_time_le_of_runs,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_runs_add_const,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_time_isBigO,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStage_srcRuns,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainBody_srcRuns,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_loops_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSource_sum_parts,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSource_sum_ge,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSource_box_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSource_core_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactSource_direct_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_runs_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_runs_time_isBigO,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStablePre_of_mid,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStablePre_framed,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStablePre_entry,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainSourceRuns,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainSrcFwd_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainSrcOpp_eventually,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_ml_counts,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_ml_writer_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_ml_stage_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_ml_lay_cost_le_gen,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_stash_le,
    ``IntegerMultBounds.MathlibTM2.Cost.compactRetuned_finStash,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainEntry_srcRuns,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainStage_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainEntry_primitive,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainDigits_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainMv_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainPoint_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainRound_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainClearCm_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainReadLen_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainOut_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMulInTime_of_main_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainChain_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainParams_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_only_inp,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainIn_projection,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainV₀_projection,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainClear_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainReset_exec,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_finish,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMain_runs_eq,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainChain_exec_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactRetunedChain_entry_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainCoeffs_words,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainCoeffs_length,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainCoeffs_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactCompleted_hostMul,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactRetunedPreTime_eq,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactRetuned_prefix_cost_le,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainDistribution_calls,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainInputDist_exec_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactMainOutput_exec_eventually,
    ``IntegerMultBounds.MathlibTM2.Fast.Main.compactRetunedPrefix_exec,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.prior_dimension_obstruction,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.margin_covers,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.layer_margin,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.twentieth_power_exceeds_sixteenth,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.next_supplier_obstruction,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.next_gaussian_obstruction,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.Eighth.margin_covers,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.Eighth.gaussian_margin,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.Eighth.supplier_obstruction,
    ``IntegerMultBounds.MathlibTM2.Cost.CompactDimension.Eighth.fourth_root_gaussian_obstruction]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
  logInfo m!"Compact-control host axiom audit passed for {names.size} contracts."
