import PlaneWave

/-!
# Axiom check

One `#print axioms` report for each main statement of every module. Every report should list
only `propext`, `Classical.choice` and `Quot.sound`; `scripts/check_axioms.ps1` (or `.sh`) runs
this file and checks that.
-/

-- PlaneWave.Certificate
#print axioms PlaneWaveCertificate.periodicMolecularCubicError
#print axioms PlaneWaveCertificate.periodicMolecularCubicConvergence
#print axioms PlaneWaveCertificate.periodicMolecularCubicAccuracyOfBasisBudget
#print axioms PlaneWaveCertificate.periodicMolecularCubicAccuracy
#print axioms PlaneWaveCertificate.periodicMolecularSectorCubicError
#print axioms PlaneWaveCertificate.periodicMolecularSectorCubicConvergence
#print axioms PlaneWaveCertificate.periodicMolecularSectorCubicAccuracyOfBasisBudget
#print axioms PlaneWaveCertificate.periodicMolecularSectorCubicAccuracy
#print axioms PlaneWaveCertificate.IsMolecularFermionicCubicGroundEnergy.le_of_cubic
#print axioms PlaneWaveCertificate.IsMolecularSpinCubicGroundEnergy.le_of_cubic
#print axioms PlaneWaveCertificate.IsCoulombSectorCubicGroundEnergy.le_of_cubic
#print axioms PlaneWaveCertificate.IsCoulombSpinCubicGroundEnergy.le_of_cubic
#print axioms PlaneWaveCertificate.molecularFiniteReferenceEnergyBound_le_explicit
#print axioms PlaneWaveCertificate.molecularGroundEnergyBudget_le_explicit
#print axioms PlaneWaveCertificate.periodicCoulombSectorCubicError
#print axioms PlaneWaveCertificate.periodicCoulombSectorCubicConvergence
#print axioms PlaneWaveCertificate.periodicCoulombSectorCubicAccuracyOfBasisBudget
#print axioms PlaneWaveCertificate.periodicCoulombSectorCubicAccuracy
#print axioms PlaneWaveCertificate.periodicCoulombCubicError
#print axioms PlaneWaveCertificate.periodicCoulombCubicConvergence
#print axioms PlaneWaveCertificate.periodicCoulombCubicAccuracyOfBasisBudget
#print axioms PlaneWaveCertificate.periodicCoulombCubicAccuracy
#print axioms PlaneWaveCertificate.coulombFiniteReferenceEnergyBound_le_explicit
#print axioms PlaneWaveCertificate.coulombGroundEnergyBudget_le_explicit
#print axioms PlaneWaveCertificate.coulombCanonicalCubicErrorConstant_le_coarse
#print axioms PlaneWaveCertificate.coulombDataCubicErrorConstant_le_coarse
#print axioms PlaneWaveCertificate.coulombDataCubicThreshold_le_poly
#print axioms PlaneWaveCertificate.molecularCanonicalCubicErrorConstant_le_coarse
#print axioms PlaneWaveCertificate.molecularDataCubicErrorConstant_le_coarse
#print axioms PlaneWaveCertificate.molecularDataCubicThreshold_le_poly
#print axioms PlaneWaveDynamics.exists_coulombPropagator
#print axioms PlaneWaveDynamics.exists_finitePropagator
#print axioms PlaneWaveDynamics.thm_dyn
#print axioms PlaneWaveDynamics.thm_dyn_rates
#print axioms PlaneWaveDynamics.thm_dyn_hchi
#print axioms PlaneWaveDynamics.thm_dyn_simple
#print axioms PlaneWaveDynamics.coulomb_observable_normalised
#print axioms PlaneWaveDynamics.coulomb_normalisation_threshold
#print axioms PlaneWaveDynamics.thm_dyn_spin
#print axioms PlaneWaveDynamics.thm_dyn_spin_rates
#print axioms PlaneWaveDynamics.thm_dyn_spin_hchi
#print axioms PlaneWaveDynamics.thm_dyn_spin_simple
#print axioms PlaneWaveDynamics.thm_dyn_spin_species
#print axioms PlaneWaveDynamics.thm_dyn_spin_species_hchi
#print axioms PlaneWaveDynamics.coulomb_observable_normalised_spin
#print axioms PlaneWaveDynamics.coulomb_normalisation_threshold_spin
#print axioms PlaneWaveDynamics.commConst_le_derivs
#print axioms PlaneWaveKinetic.thm_mult_gal
#print axioms PlaneWaveKinetic.thm_mult_cap
#print axioms PlaneWaveKinetic.stopping_galerkin
#print axioms PlaneWaveKinetic.stopping_window
#print axioms PlaneWaveSpin.thm_mult_gal_spin
#print axioms PlaneWaveSpin.thm_mult_cap_spin
#print axioms PlaneWaveSpin.stopping_galerkin_spin
#print axioms PlaneWaveSpin.stopping_window_spin

-- PlaneWave.GridCore
#print axioms PlaneWaveGrid.grid_galerkin_energy
#print axioms PlaneWaveGrid.isSecRitz_Hpos_iff

-- PlaneWave.Grid
#print axioms PlaneWaveGrid.periodicCoulombGridError
#print axioms PlaneWaveGrid.periodicCoulombSectorGridError
#print axioms PlaneWaveGrid.periodicMolecularGridError
#print axioms PlaneWaveGrid.periodicMolecularSectorGridError
#print axioms PlaneWaveGrid.periodicCoulombKernelGridError
#print axioms PlaneWaveGrid.periodicCoulombSectorKernelGridError
#print axioms PlaneWaveGrid.periodicMolecularKernelGridError
#print axioms PlaneWaveGrid.periodicMolecularSectorKernelGridError
#print axioms PlaneWaveGrid.grid_galerkin_energy
#print axioms PlaneWaveGrid.isSecRitz_Hpos_iff
#print axioms PlaneWaveGrid.coulombGridErrorConstant_le_poly
#print axioms PlaneWaveGrid.coulombGridThreshold_le_poly
#print axioms PlaneWaveGrid.gridErrorConstant_le_poly
#print axioms PlaneWaveGrid.gridThreshold_le_poly
#print axioms PlaneWaveFullKernel.periodicCoulombSectorFullKernelError
#print axioms PlaneWaveFullKernel.periodicCoulombFullKernelError
#print axioms PlaneWaveFullKernel.periodicMolecularSectorFullKernelError
#print axioms PlaneWaveFullKernel.periodicMolecularFullKernelError
#print axioms PlaneWaveFullKernel.fullKernelErrorConstant_le_poly
#print axioms PlaneWaveFullKernel.fullKernelBasisErrorConstant_le_poly
#print axioms PlaneWaveFullKernel.fullKernelThreshold_le_poly
#print axioms PlaneWaveFullKernel.fullKernelImpConstant₁_le_poly
#print axioms PlaneWaveFullKernel.fullKernelImpConstant₂_le_poly
#print axioms PlaneWaveFullKernel.fullKernelErrorConstant_le_poly_bo
#print axioms PlaneWaveFullKernel.fullKernelBasisErrorConstant_le_poly_bo
#print axioms PlaneWaveFullKernel.fullKernelThreshold_le_poly_bo
#print axioms PlaneWaveFullKernel.fullKernelImpConstant₁_le_poly_bo
#print axioms PlaneWaveFullKernel.fullKernelImpConstant₂_le_poly_bo
#print axioms PlaneWaveFullKernel.coulombGridErrorConstant_le_polyVar
#print axioms PlaneWaveFullKernel.coulombGridThreshold_le_polyVar
#print axioms PlaneWaveFullKernel.fullKernelCorrSummable_exists
#print axioms PlaneWaveGridDynamics.exists_posPropagator
#print axioms PlaneWaveGridDynamics.thm_grid_dyn
#print axioms PlaneWaveGridDynamics.thm_grid_dyn_min
#print axioms PlaneWaveGridDynamics.grid_observable_normalised
#print axioms PlaneWaveGridDynamics.grid_normalisation_threshold
#print axioms PlaneWaveGridDynamics.thm_grid_dyn_sharp
#print axioms PlaneWaveGridDynamics.thm_grid_dyn_sharp_min
#print axioms PlaneWaveKinetic.thm_mult_grid
#print axioms PlaneWaveKinetic.thm_mult_cap_grid
#print axioms PlaneWaveKinetic.stopping_grid
#print axioms PlaneWaveKinetic.stopping_window_grid
#print axioms PlaneWaveSpin.thm_grid_dyn_spin
#print axioms PlaneWaveSpin.thm_grid_dyn_min_spin
#print axioms PlaneWaveSpin.thm_grid_dyn_sharp_spin
#print axioms PlaneWaveSpin.thm_grid_dyn_sharp_min_spin
#print axioms PlaneWaveSpin.grid_observable_normalised_spin
#print axioms PlaneWaveSpin.grid_normalisation_threshold_spin
#print axioms PlaneWaveSpin.thm_mult_grid_spin
#print axioms PlaneWaveSpin.thm_mult_cap_grid_spin
#print axioms PlaneWaveSpin.stopping_grid_spin
#print axioms PlaneWaveSpin.stopping_window_grid_spin

-- PlaneWave.Source.BulkGeneratorPrototype
#print axioms FluxSourceTest.gap
#print axioms FluxSourceTest.lattice_gap
#print axioms FluxSourceTest.tailFn_summable_and_le
#print axioms FluxSourceTest.SchurBound.exp_mem_unitary
#print axioms FluxSourceTest.bulkGenerator
#print axioms FluxSourceTest.vbK_hs
#print axioms FluxSourceTest.exp_sigma_preserves_domain
#print axioms FluxSourceTest.bulkGenerator_release

-- PlaneWave.Source.SpectralLayer
#print axioms FSSpectral.specleak
#print axioms FSSpectral.tavg_bound
#print axioms FSSpectral.tavg_window_bound

-- PlaneWave.Source.LoewnerHeinz
#print axioms FluxSourceTest.cfc_apply_eigen
#print axioms FluxSourceTest.rpow_apply_eigen
#print axioms FluxSourceTest.rpow_apply_basis
#print axioms FluxSourceTest.norm_rpow_le_of_norm_le
#print axioms FluxSourceTest.norm_ePow_le_of_norm_ePow_le
#print axioms FluxSourceTest.norm_sq_ePow

-- PlaneWave.Source.HotContentAbstract
#print axioms FSSpectral.tavg_hot_abstract

-- PlaneWave.Source.LatticeSums
#print axioms FSLattice.card_box
#print axioms FSLattice.mem_box_of_lsq_le
#print axioms FSLattice.card_shell_le
#print axioms FSLattice.lsq_ge_of_not_mem
#print axioms FSLattice.sum_inv_lsq_box_le
#print axioms FSLattice.sum_inv_lsq_ball_le
#print axioms FSLattice.sum_weight_le
#print axioms FSLattice.summable_weight
#print axioms FSLattice.tsum_weight_le
#print axioms FSLattice.sum_norm_le_weighted
#print axioms FSLattice.sum_norm_le_weighted_shift
#print axioms FSLattice.sum_norm_le_weighted_sub
#print axioms FSLattice.card_euclid_shell_le

-- PlaneWave.Source.QtailRecursion
#print axioms FSQtail.qtail_recursion

-- PlaneWave.Source.GalerkinSpectralLayer
#print axioms FSGalerkin.HN_eq_kin_add
#print axioms FSGalerkin.potential_le_wt
#print axioms FSGalerkin.HN_lower

-- PlaneWave.Source.RetainedHamiltonian
#print axioms FSGalerkin.Vret_le_wt
#print axioms FSGalerkin.Hret_lower
#print axioms FSGalerkin.wt_le_holder
#print axioms FSGalerkin.wt_one_le_of_quasi

-- PlaneWave.Source.ChannelKernels
#print axioms FSChannel.sum_tail_inv_pow_four_le
#print axioms FSChannel.schur_sum_sq
#print axioms FSChannel.near_sum_le
#print axioms FSChannel.far_sum_le
#print axioms FSChannel.norm_wop_le

-- PlaneWave.Source.RegisterStructure
#print axioms FSGalerkin.Hbar_regLocal
#print axioms FSGalerkin.Va_registerBound
#print axioms FSGalerkin.Hbar_coercive
#print axioms FSGalerkin.norm_le_of_slice_coercive

-- PlaneWave.Source.QuasiEigenstateTails
#print axioms FSGalerkin.isChannel_nuc
#print axioms FSGalerkin.isChannel_pair
#print axioms FSGalerkin.norm_regMul_Va_le
#print axioms FSGalerkin.qtail_rec
#print axioms FSGalerkin.qtail
#print axioms FSGalerkin.regTail_le_of_quasi

-- PlaneWave.Source.TimeAveragedHotContent
#print axioms FSGalerkin.norm_sq_hotProj_le
#print axioms FSGalerkin.hot_sq_le_of_quasi
#print axioms FSGalerkin.graph_le
#print axioms FSGalerkin.tavg_hot

-- PlaneWave.Source.WeightedMoments
#print axioms FSDatum.moment_le_of_tails
#print axioms FSDatum.moment_quarter_le_of_tails

-- PlaneWave.Source.GoodStates
#print axioms FSGalerkin.datum_support
#print axioms FSGalerkin.norm_datum_le
#print axioms FSGalerkin.wt_datum_sq_le

-- PlaneWave.Source.TavgQuarterExplicit
#print axioms FSGalerkin.tavg_quarter_explicit
#print axioms FSGalerkin.tavgScale_of_large

-- PlaneWave.Source.RetainedFlow
#print axioms FSGalerkin.norm_retFlow
#print axioms FSGalerkin.retFlow_add
#print axioms FSGalerkin.hasDerivAt_retFlow
#print axioms FSGalerkin.wt_one_le_shifted
#print axioms FSGalerkin.retflow
#print axioms FSGalerkin.quarter_flow
#print axioms FSGalerkin.src_nc1
#print axioms FSGalerkin.src_nc1_explicit

-- PlaneWave.Source.ChannelPotentials
#print axioms FSNormal.norm_potKernel_le
#print axioms FSNormal.potential_apply
#print axioms FSNormal.potKernel_conj

-- PlaneWave.Source.BulkGenerator
#print axioms FSNormal.channel_gap
#print axioms FSNormal.sigK_schur
#print axioms FSNormal.Sig_skew_unitary
#print axioms FSNormal.comm_kernel
#print axioms FSNormal.stateMap_SigD
#print axioms FSNormal.kinetic_comm

-- PlaneWave.Source.Conjugation
#print axioms FSConj.norm_Bi_taylor_le
#print axioms FSConj.norm_conj_taylor_le
#print axioms FSConj.conj_unbounded

-- PlaneWave.Source.TransformedHamiltonian
#print axioms FSNormal.sig_W
#print axioms FSNormal.hHG
#print axioms FSNormal.conj_H
#print axioms FSNormal.inner_Bcorr
#print axioms FSNormal.dressed_hasDerivAt

-- PlaneWave.Source.AssemblyIdentity
#print axioms FSNormal.dH_symm
#print axioms FSNormal.fT_eq
#print axioms FSNormal.duhamel_weak
#print axioms FSNormal.assembly

-- PlaneWave.Source.HardyBound
#print axioms FSNormal.potential_form_bound
#print axioms FSNormal.norm_W_liftQ_le
#print axioms FSNormal.norm_Vb_le

-- PlaneWave.Source.FibreBounds
#print axioms FSNormal.fibre_gram
#print axioms FSNormal.form_sig_Q_le
#print axioms FSNormal.norm_sig_Q_state_le
#print axioms FSNormal.form_sig_Q_state_le

-- PlaneWave.Source.RetainedCorrection
#print axioms FSNormal.norm_Zw_le
#print axioms FSNormal.norm_X1_le
#print axioms FSNormal.norm_dH_le

-- PlaneWave.Source.ExponentialBounds
#print axioms FSConj.norm_exp_sub_one_apply_le
#print axioms FSConj.norm_exp_sub_one_sub_apply_le
#print axioms FSConj.norm_exp_neg_sub_one_add_apply_le

-- PlaneWave.Source.DressedState
#print axioms FSConj.mul_Jx
#print axioms FSConj.norm_Jx_apply_le
#print axioms FSNormal.sig_split
#print axioms FSNormal.dressed_exterior
#print axioms FSNormal.dressed_lift
#print axioms FSNormal.dressed_tails

-- PlaneWave.Source.GoodStatesBothSpaces
#print axioms FSNormal.fgood_W
#print axioms FSNormal.traj_fgood
#print axioms FSNormal.ext_good
#print axioms FSNormal.isGood_perturb
#print axioms FSNormal.regTail_WN_le
#print axioms FSNormal.good_stab

-- PlaneWave.Source.ObservableNonsecular
#print axioms FSNormal.Ofull_emb
#print axioms FSNormal.T4_le
#print axioms FSNormal.T5_le
#print axioms FSNormal.T2_le
#print axioms FSNormal.Acorr_le

-- PlaneWave.Source.FirstRetainedCorrection
#print axioms FSNormal.norm_dH_le_wt
#print axioms FSNormal.norm_sig_emb_wt_le
#print axioms FSNormal.Vb_exterior
#print axioms FSNormal.PSigVbR
#print axioms FSNormal.norm_Zw_emb_le
#print axioms FSNormal.norm_Zw_adj_emb_le
#print axioms FSNormal.norm_Vb_emb_le

-- PlaneWave.Source.SourceTerm
#print axioms FSNormal.fT_decomp
#print axioms FSNormal.source_pairing
#print axioms FSNormal.pair_Zw_le
#print axioms FSNormal.pair_Zw_adj_le

-- PlaneWave.Source.TruncatedObservable
#print axioms FSNormal.obs_reduction

-- PlaneWave.Source.MixedClass
#print axioms FSKernel.norm_divK_HL_wt_le
#print axioms FSNormal.Hmix_cold
#print axioms FSNormal.Hmix_hot
#print axioms FSNormal.Hmix_eq_kop
#print axioms FSNormal.Hmix_split
#print axioms FSNormal.comm_Sig2mix
#print axioms FSNormal.norm_Zw_emb_wt_le
#print axioms FSNormal.norm_Hmix_le
#print axioms FSNormal.norm_SHL_wt_le
#print axioms FSNormal.norm_Sig2mix_le
#print axioms FSNormal.norm_inner_HmixRes_le
#print axioms FSNormal.norm_Hmix_wt_le

-- PlaneWave.Source.PotentialTails
#print axioms FSDatum.moment_le_of_tails1
#print axioms FSNormal.norm_res_hot_WN_le
#print axioms FSNormal.wt_res_low_WN_sq_le
#print axioms FSNormal.kato_pair

-- PlaneWave.Source.TaylorRemainder
#print axioms FSConj.norm_cj_sub_tp_apply_le
#print axioms FSConj.norm_Bi_sub_bp_apply_le
#print axioms FSNormal.ext_ad2_Vb
#print axioms FSNormal.dH_decomp
#print axioms FSNormal.norm_DH4_le

-- PlaneWave.Source.RetainedLedger
#print axioms FSConj.ledger_identity
#print axioms FSConj.norm_inner_ledger_le

-- PlaneWave.Source.RetainedRotations
#print axioms FSNormal.dHc_eq
#print axioms FSNormal.cm_Z2_A
#print axioms FSNormal.Z2_skew
#print axioms FSNormal.Hpp_mul_U
#print axioms FSNormal.norm_inner_cm_Z2m_V_le
#print axioms FSNormal.norm_inner_cm_S3_V_le

-- PlaneWave.Source.RefinedBudgets
#print axioms FSNormal.isGood_perturb'
#print axioms FSNormal.good_of_kin_tails
#print axioms FSNormal.kin_tails_of_decomp
#print axioms FSNormal.good_of_decomp
#print axioms FSNormal.good_stab'

-- PlaneWave.Source.LedgerGoodStates
#print axioms FSNormal.ledD_bound
#print axioms FSNormal.norm_inner_Hpp_good

-- PlaneWave.Source.RetainedComparison
#print axioms norm_quad_sub_le
#print axioms FSNormal.duhamel_rot
#print axioms FSNormal.T1_le

-- PlaneWave.Source.TrajectoryBudgets
#print axioms FSNormal.Mtraj_le
#print axioms FSNormal.traj_good
#print axioms FSNormal.aT_bounds
#print axioms FSNormal.chi_good
#print axioms FSNormal.rot_good
#print axioms FSNormal.psiN_good
#print axioms FSNormal.psiNr_good

-- PlaneWave.Source.RetainedComparisonExplicit
#print axioms FSNormal.ledK_le
#print axioms FSNormal.flow_datum_bounds
#print axioms FSNormal.T1_explicit

-- PlaneWave.Source.SourceNonsecularTerms
#print axioms FSNormal.norm_fT_le
#print axioms FSNormal.norm_aT_sub_chi_le

-- PlaneWave.Source.SourceNonsecularExplicit
#print axioms FSNormal.T3_explicit

-- PlaneWave.Source.Src3Terms
#print axioms FSNormal.T2_explicit
#print axioms FSNormal.T4_explicit
#print axioms FSNormal.T5_explicit

-- PlaneWave.Source.Src3Explicit
#print axioms FSNormal.src3_explicit

-- PlaneWave.Source.Src3Conditional
#print axioms FSAsymp.thm_src3

-- PlaneWave.Source.Stopping3Conditional
#print axioms FSAsymp.initial_error
#print axioms FSAsymp.cor_stopping3

-- PlaneWave.Source.FirstSourceRound
#print axioms FSSrc1.wt_bdatum_sq_le_tails
#print axioms FSSrc1.phi_norms
#print axioms FSSrc1.src_decomp
#print axioms FSSrc1.src_pair
#print axioms FSSrc1.prop_src1
#print axioms FSSrc1.thm_src1_explicit
#print axioms FSSrc1.thm_src1

-- PlaneWave.Source.SourceLeftovers
#print axioms FSSrc1.wt_le_holder_half
#print axioms FSSrc1.regTail_le_wt
#print axioms FSSrc1.phi_interp
#print axioms FSSrc1.phi_eps
#print axioms FSSrc1.phi_tail
#print axioms FSSrc1.a2_form
#print axioms FSSrc1.a2_bound

-- PlaneWave.Flux.ForceForm
#print axioms FSFlux.norm_Gf_le
#print axioms FSFlux.form_le_norm_mul
#print axioms FSFlux.flux_id
#print axioms FSFlux.flux_nc
#print axioms FSFlux.flux_bd
#print axioms FSFlux.flux_id_galerkin
#print axioms FSFlux.thm_flux

-- PlaneWave.Flux.FluxDressing
#print axioms FSFlux.comm_Y
#print axioms FSFlux.elim_deriv
#print axioms FSFlux.elim_integral
#print axioms FSFlux.Yop_truncQ_apply
#print axioms FSFlux.norm_yK_le
#print axioms FSFlux.norm_YQ_sq_le
#print axioms FSFlux.norm_YQ_le
#print axioms FSFlux.inner_Y_self
#print axioms FSFlux.elim_bdry_state
#print axioms FSFlux.thm_elim_bdry
#print axioms FSFlux.thm_elim

-- PlaneWave.Flux.Flux2Split
#print axioms FSFlux.Vb_split
#print axioms FSFlux.Gb_eq
#print axioms FSFlux.flux2_split
#print axioms FSFlux.flux_nc_gen
#print axioms FSFlux.flux_nc4
#print axioms FSFlux.thm_flux2_of_phase

-- PlaneWave.Flux.PhaseTools
#print axioms FSFlux.flat_sum2_le
#print axioms FSFlux.flat_tsum2_le
#print axioms FSFlux.fibre_amgm
#print axioms FSFlux.moment_Q
#print axioms FSFlux.norm_YQ_sq_le_s
#print axioms FSFlux.regSymbol_diff_le
#print axioms FSFlux.Ek_diff_le
#print axioms FSFlux.sY_diff_le

-- PlaneWave.Flux.PhaseBulkBlock
#print axioms FSFlux.inner_Wlq_YQ
#print axioms FSFlux.cK_antiherm
#print axioms FSFlux.norm_cK_antiherm_le
#print axioms FSFlux.fibre_grad_le
#print axioms FSFlux.bulk_im_le

-- PlaneWave.Flux.Flux2
#print axioms FSFlux.nrm_b
#print axioms FSFlux.W_tails
#print axioms FSFlux.Wf_re_eq
#print axioms FSFlux.inner_W_Y_split
#print axioms FSFlux.tail_C1_le
#print axioms FSFlux.norm_YQW_le
#print axioms FSFlux.bulk_good_le
#print axioms FSFlux.phase_state
#print axioms FSFlux.thm_phase
#print axioms FSFlux.thm_flux2

-- PlaneWave.SourceBand.ThinShellCounts
#print axioms FSBand.thin_count
#print axioms FSBand.thin_count_le
#print axioms FSBand.thin_count_cube
#print axioms FSBand.thin_count_cube_le
#print axioms FSBand.thinschur_gen
#print axioms FSBand.thinschur
#print axioms FSBand.thinschur_cube

-- PlaneWave.SourceBand.Band
#print axioms FSBand.shE_count
#print axioms FSBand.shC_count
#print axioms FSBand.far_band_finite
#print axioms FSBand.shell_state_le
#print axioms FSBand.near_band
#print axioms FSBand.far_band
#print axioms FSBand.band_W
#print axioms FSBand.band_exact
#print axioms FSBand.band_trunc

-- PlaneWave.SourceBand.BandGalerkin
#print axioms FSBand.fgood_cubeLift
#print axioms FSBand.band_of_decomp
#print axioms FSBand.retained_decomp
#print axioms FSBand.band_stab_gen
#print axioms FSBand.band_stab
#print axioms FSBand.band_stab_A
#print axioms FSBand.band_galerkin
#print axioms FSBand.band_backward

-- PlaneWave.SourceBand.SpectatorBound
#print axioms FSBand.chC_sysCh
#print axioms FSBand.potKernel_sysCh_le
#print axioms FSBand.potKernel_eq_sum
#print axioms FSBand.W_eq_sum_Wch
#print axioms FSBand.norm_Wch_sq_le
#print axioms FSBand.Wch_shMask
#print axioms FSBand.band_spectator

-- PlaneWave.SourceBand.MovingRegister
#print axioms FSBand.sum_dyadic_ind
#print axioms FSBand.sum_pow_two_le
#print axioms FSBand.sum_inv_pow_two_le
#print axioms FSBand.wide_band
#print axioms FSBand.dyadic_decomp
#print axioms FSBand.band_moved
#print axioms FSBand.band_K2

-- PlaneWave.SourceBand.SrcRes
#print axioms FSBand.slabF_swap
#print axioms FSBand.resK_schur
#print axioms FSBand.resK_short
#print axioms FSBand.resK_eq_zero_of_ge
#print axioms FSBand.Kres_le_log
#print axioms FSBand.src_res_le
#print axioms FSBand.prop_src_res

-- PlaneWave.SourceBand.BandTails
#print axioms FSChannel.norm_wop_band_le
#print axioms FSGalerkin.norm_regMul_Va_le_of
#print axioms FSGalerkin.card_bandSet_le
#print axioms FSGalerkin.band_le_resolvent
#print axioms FSGalerkin.qtail_band_raw
#print axioms FSGalerkin.qtail_band
#print axioms FSGalerkin.band_le_of_quasi
#print axioms FSGalerkin.bandProj_sq_le_of_quasi
#print axioms FSGalerkin.tavg_band
#print axioms FSGalerkin.tavg_band_explicit
#print axioms FSGalerkin.tavg_half_explicit
#print axioms FSBand.phi_band_at_t

-- PlaneWave.SamePair.LatticeCounts
#print axioms FSLattice.pin_two_sided
#print axioms FSLattice.window_box_count
#print axioms FSLattice.h3_core
#print axioms FSLattice.slab2_count

-- PlaneWave.SamePair.SameChannelKernel
#print axioms FSNormal.kop_kmul
#print axioms FSNormal.norm_h3cK_le

-- PlaneWave.SamePair.LatticeSums
#print axioms FSLattice.h3_diag_core
#print axioms FSLattice.sig3_core
#print axioms FSLattice.log_ceil_le

-- PlaneWave.SamePair.ThirdOrderKernel
#print axioms FSNormal.H3first_matK
#print axioms FSNormal.h3fL_eq_sum
#print axioms FSNormal.h3fW_diag_conj
#print axioms FSNormal.norm_h3fW_le

-- PlaneWave.SamePair.RetainedThirdOrder
#print axioms FSNormal.VN_eq_kop
#print axioms FSNormal.H3ret_decomp
#print axioms FSNormal.h3spK_conj
#print axioms FSNormal.norm_h3spK_le
#print axioms FSNormal.norm_h3spK_diag_le

-- PlaneWave.SamePair.Res3
#print axioms FSNormal.H3sp_split
#print axioms FSNormal.norm_r3_shell_le
#print axioms FSNormal.norm_H3resSp_good

-- PlaneWave.SamePair.ThirdGenerator
#print axioms FSNormal.comm_Sig3sp
#print axioms FSNormal.comm_Sig3sp'
#print axioms FSNormal.inner_Sig3sp
#print axioms FSNormal.norm_Sig3sp_le

-- PlaneWave.SamePair.Package
#print axioms FSAsymp.pl_Bh3
#print axioms FSAsymp.pl_CR3
#print axioms FSAsymp.pl_CS3
#print axioms FSNormal.same_pair_package

-- PlaneWave.Observable.SecondOrder
#print axioms FSNormal.obs_hop_le
#print axioms FSNormal.norm_obsK_le
#print axioms FSNormal.chan_trace_le
#print axioms FSNormal.obs2
#print axioms FSNormal.obs2_good
#print axioms FSAsymp.pl_Cobs2

-- PlaneWave.FluxBox.BigBox
#print axioms FSFlux.Gf_cubeLift₂
#print axioms FSFlux.flux_box
#print axioms FSFlux.elim_box

-- PlaneWave.FluxBox.Flux3
#print axioms FSFlux.abs_im_CC_good_le
#print axioms FSFlux.abs_comm_Y3_good_le
#print axioms FSFlux.ledger_box_le
#print axioms FSFlux.flux_box_total
#print axioms FSFlux.flux_box_scaled
#print axioms FSFlux.thm_flux3

-- PlaneWave.Observable.ThirdOrderSamePair
#print axioms FSNormal.norm_obs3K_le
#print axioms FSNormal.obs3sp
#print axioms FSNormal.obs3sp_good
#print axioms FSAsymp.pl_Cobs3
#print axioms FSNormal.lem_obs3_sp

-- PlaneWave.FluxSourceSpin
#print axioms FSSpin.sum_Xi_sq_le
#print axioms FSSpin.XiS_eq_norm
#print axioms FSSpin.integral_GfS
#print axioms FSSpin.thm_flux_spin
#print axioms FSSpin.thm_flux2_spin
#print axioms FSSpin.thm_flux3_spin
#print axioms FSSpin.thm_src1_spin
#print axioms FSSpin.thm_src3_spin
#print axioms FSSpin.cor_stopping3_spin

-- PlaneWave.KineticCompletion.InverseMismatch
#print axioms FSLattice.sep_row
#print axioms FSLattice.inv_mismatch_row
#print axioms FSLattice.inv_mismatch_col
#print axioms FSLattice.wschur
#print axioms FSLattice.sum_box_inv_le

-- PlaneWave.KineticCompletion.CrossCommutators
#print axioms FSNormal.exists_dir
#print axioms FSNormal.lam_mul_le
#print axioms FSNormal.norm_Zj_le
#print axioms FSNormal.dir_hardy
#print axioms FSNormal.norm_kop_hardy
#print axioms FSNormal.norm_crossX_le

-- PlaneWave.KineticCompletion.FirstRotationWords
#print axioms FSNormal.sep_inP
#print axioms FSNormal.h3fW_eq
#print axioms FSNormal.norm_TA_le
#print axioms FSNormal.norm_TB_le
#print axioms FSNormal.norm_TC_le
#print axioms FSNormal.norm_word_le
#print axioms FSNormal.norm_H3mp_le

-- PlaneWave.KineticCompletion.QuarterPowerWeights
#print axioms FSLattice.sum_inv_qd_le
#print axioms FSNormal.col_sig3_weighted
#print axioms FSNormal.norm_wt_Sig3sp_le
#print axioms FSNormal.weighted_Sig3sp_good

-- PlaneWave.KineticCompletion.Completion
#print axioms FSAsymp.exists_logK_bound
#print axioms FSAsymp.pl_CW
#print axioms FSAsymp.completion
#print axioms FSAsymp.thm_src3_uncond
#print axioms FSAsymp.cor_stopping3_uncond
#print axioms FSSpin.thm_src3_spin_uncond
#print axioms FSSpin.cor_stopping3_spin_uncond
#print axioms FSNormal.exists_evoData

-- PlaneWave.KineticCompletion.CompletionClauses
#print axioms FSLattice.kato_sum_le
#print axioms FSNormal.dir_kato
#print axioms FSNormal.form_VN_le
#print axioms FSNormal.norm_formW_le
#print axioms FSNormal.weighted_Sig3sp_E14
#print axioms FSNormal.inner_R3
#print axioms FSLattice.relativeD
#print axioms FSLattice.relativeD_log
#print axioms FSNormal.norm_Sj_le
#print axioms FSNormal.norm_Sj_lam_le
#print axioms FSAsymp.Sdirection_orders
#print axioms FSAsymp.completion_full

-- PlaneWave.Auxiliary.FluxSourceClauses
#print axioms FluxSourceTest.gap_sharp
#print axioms FSLattice.pin_sharp
#print axioms FSNormal.acorr_PR
#print axioms FSNormal.norm_acorr_PR_le
#print axioms FSNormal.flow_datum_interp
#print axioms FSSpectral.tavg_mass

-- PlaneWave.Auxiliary.DressedTails
#print axioms FSNormal.col_sig_weighted2_le
#print axioms FSNormal.form2_sig_Q_state_le
#print axioms FSNormal.form2_sig_Q_le
#print axioms FSNormal.dressed_kin_tail
#print axioms FSNormal.dressed_half_tail
#print axioms FSNormal.dressed_r_support
#print axioms FSNormal.dressed_energy_bounds
#print axioms FSAsymp.pl_eT
#print axioms FSAsymp.pl_half_tail
#print axioms FSAsymp.pl_theta_r
#print axioms FSAsymp.dressed_tails_logfree

-- PlaneWave.Auxiliary.LogFreePhi
#print axioms FSNormal.phiSC_eq
#print axioms FSNormal.phi_logfree_high
#print axioms FSNormal.phi_logfree_low

-- PlaneWave.Auxiliary.FourierDomination
#print axioms FSNormal.fourier_domination
#print axioms FSNormal.dominated_pair_hardy
#print axioms FSNormal.dominated_single_hardy
#print axioms FSNormal.grid_KR

-- PlaneWave.Auxiliary.AliasGrid
#print axioms FSNormal.alias_bound
#print axioms FSNormal.alias_bound_restricted
#print axioms FSNormal.norm_gridDiag_le
#print axioms FSNormal.gridDiag_apply
#print axioms FSNormal.tail_gridDiag_le
#print axioms FSNormal.grid_form_lower
#print axioms FSNormal.grid_lower_bound
#print axioms FSNormal.grid_graph_equivalence

-- PlaneWave.Auxiliary.PotentialTails
#print axioms FSNormal.fullH2Sq_le
#print axioms FSNormal.tail_domination
#print axioms FSNormal.tail_pair_dominated
#print axioms FSNormal.tail_single_dominated
#print axioms FSNormal.grid_tail
#print axioms FSNormal.grid_potential_tail
#print axioms FSNormal.grid_potential_tail_explicit

-- PlaneWave.Auxiliary.GalerkinDynamics
#print axioms PlaneWaveDynamics.coulomb_normlevel_full
#print axioms PlaneWaveKinetic.cube_tails_all
#print axioms PlaneWaveKinetic.cube_supTails_all
#print axioms PlaneWaveDynamics.flow_commute
#print axioms PlaneWaveDynamics.galerkin_flow_isSector
#print axioms PlaneWaveDynamics.galerkin_trajectory_isSector
#print axioms PlaneWaveDynamics.coulombPMap_isSelfAdjoint

-- PlaneWave.FreeBoundary.Scaling
#print axioms FreeBoundary.scaling_low
#print axioms FreeBoundary.scaling_tail
#print axioms FreeBoundary.scaling_tail_tsum
#print axioms FreeBoundary.scaling_moment2
#print axioms FreeBoundary.scaling_moment4
#print axioms FreeBoundary.sobolev_weight_sum
#print axioms FreeBoundary.slice_sobolev

-- PlaneWave.FreeBoundary.RangeCut
#print axioms FreeBoundary.gFT_eq_sin
#print axioms FreeBoundary.norm_gFT_le
#print axioms FreeBoundary.gFT_zero
#print axioms FreeBoundary.rangecut
#print axioms FreeBoundary.ghat_zero_le_half
#print axioms FreeBoundary.scaling_moment4_gL

-- PlaneWave.FreeBoundary.CubeHamiltonian
#print axioms FreeBoundary.norm_gLk_le
#print axioms FreeBoundary.gLpot_isSymmetric
#print axioms FreeBoundary.gLpot_h1Bound
#print axioms FreeBoundary.gLpot_massBound
#print axioms FreeBoundary.gLpot_tail_bound
#print axioms FreeBoundary.gL_eigen_fullH2Sq_le
#print axioms FreeBoundary.gL_cubic_energy_bound

-- PlaneWave.FreeBoundary.GridCoreGeneral
#print axioms PlaneWaveGridG.grid_galerkin_energy
#print axioms PlaneWaveGridG.isSecRitz_Hpos_iff

-- PlaneWave.FreeBoundary.TorusGroundEnergy
#print axioms FreeBoundary.gLham_eq_latticeKernel
#print axioms FreeBoundary.gLham_preserves_sector
#print axioms FreeBoundary.transport_form
#print axioms FreeBoundary.cube_ground_to_cubic
#print axioms FreeBoundary.exists_gLTorusGroundEnergy
#print axioms FreeBoundary.tendsto_cube_ground
#print axioms FreeBoundary.gL_cubic_error
#print axioms FreeBoundary.gL_sector_cubic_error

-- PlaneWave.FreeBoundary.GridEnergy
#print axioms PlaneWaveGridG.Hgal_regUnitary_gL
#print axioms PlaneWaveGridG.gLSectorKernelGridError
#print axioms PlaneWaveGridG.gLSectorGridError

-- PlaneWave.FreeBoundary.RetainedRegion
#print axioms FreeBoundary.niDist_eq_norm
#print axioms FreeBoundary.retained_potential
#print axioms FreeBoundary.mFourierCoeff_gLtorus
#print axioms FreeBoundary.mFourierCoeff_gLtorus_zero

-- PlaneWave.FreeBoundary.PositionPotential
#print axioms FreeBoundary.memLp_gLtorus
#print axioms FreeBoundary.mFourierCoeff_gLtorus0
#print axioms FreeBoundary.gLFourierPotential_fourierCoeff

-- PlaneWave.FreeBoundary.CompletedHamiltonian
#print axioms FreeBoundary.exists_gLFourierH2Operator
#print axioms FreeBoundary.gL_variational_H2
#print axioms FreeBoundary.gLPositionPotentialH2_pointwise
#print axioms FreeBoundary.gL_variational_C2

-- PlaneWave.FreeBoundary.Transplant
#print axioms FreeBoundary.contDiff_perLift
#print axioms FreeBoundary.integral_transplant
#print axioms FreeBoundary.contDiffKinetic_transplant
#print axioms FreeBoundary.gLFourierPotential_eq_freePot
#print axioms FreeBoundary.free_transplant_bound
#print axioms FreeBoundary.free_upper_of_trial

-- PlaneWave.FreeBoundary.UpperComposite
#print axioms FreeBoundary.free_grid_upper

-- PlaneWave.FreeBoundary.IMS
#print axioms FreeBoundary.integral_freeKinetic_mul_conj
#print axioms FreeBoundary.gradForm_ims
#print axioms FreeBoundary.freeEnergy_ims
#print axioms FreeBoundary.retained_trial
#print axioms FreeBoundary.free_upper_ims

-- PlaneWave.FreeBoundary.LocalisationPair
#print axioms FreeBoundary.stdLocPair
#print axioms FreeBoundary.locConst_le
#print axioms FreeBoundary.free_upper_agmon
#print axioms FreeBoundary.free_grid_upper_agmon

-- PlaneWave.FreeBoundary.TorusIMS
#print axioms FreeBoundary.torus_kinetic_by_parts
#print axioms FreeBoundary.tGrad_ims
#print axioms FreeBoundary.torusEnergy_ims
#print axioms FreeBoundary.torus_variational

-- PlaneWave.FreeBoundary.LowerBound
#print axioms FreeBoundary.tDR_cell
#print axioms FreeBoundary.stdTorusLocPair
#print axioms FreeBoundary.transplantFun_revT
#print axioms FreeBoundary.transplant_torusEnergy
#print axioms FreeBoundary.free_lower_torus
#print axioms FreeBoundary.free_grid_two_sided
#print axioms FreeBoundary.free_grid_exponential

-- PlaneWave.FreeBoundary.UniformGridCore
#print axioms PlaneWaveGridG.sum_sobolevP_le
#print axioms PlaneWaveGridG.grid_galerkin_energyP

-- PlaneWave.FreeBoundary.UniformCubic
#print axioms PlaneWaveCertificate.finitePlaneWave_hasOneParticleInverseH2WeightBoundP
#print axioms PlaneWaveCertificate.finiteElectronPairCoulombOperator_tail_bound_any_referenceP
#print axioms PlaneWaveCertificate.referenceCoulombOperator_tail_bound_two_scaleP
#print axioms FreeBoundary.gLpot_tail_boundP
#print axioms FreeBoundary.gL_cubic_energy_boundP
#print axioms FreeBoundary.gL_sector_cubic_errorP

-- PlaneWave.FreeBoundary.UniformGridEnergy
#print axioms PlaneWaveGridG.gLGridCoupling_eq
#print axioms PlaneWaveGridG.gLCubicConstP_le_U
#print axioms PlaneWaveGridG.gLSectorKernelGridErrorU
#print axioms PlaneWaveGridG.gLSectorGridErrorU

-- PlaneWave.FreeBoundary.UniformFreeEnergy
#print axioms FreeBoundary.free_grid_two_sidedU
#print axioms FreeBoundary.free_grid_exponentialU

-- PlaneWave.FreeBoundary.Dynamics
#print axioms FreeBoundary.duhamel_phase
#print axioms FreeBoundary.BoxWeight.inner_cutL2
#print axioms FreeBoundary.weak_comm_identity
#print axioms FreeBoundary.Cutoff.norm_commT_le
#print axioms FreeBoundary.transplant_hasGLHamiltonian
#print axioms FreeBoundary.BoxWeight.inner_cutL2_mulCLM
#print axioms FreeBoundary.free_dyn_torus

-- PlaneWave.FreeBoundary.Propagator
#print axioms FreeBoundary.exists_fourierPropagator_of_relBound
#print axioms FreeBoundary.gLH2_symm
#print axioms FreeBoundary.gL_potential_sq_le_quarter
#print axioms FreeBoundary.hasGLHamiltonian_iff_H2
#print axioms FreeBoundary.exists_gLPropagator
#print axioms FreeBoundary.free_dyn_gL

-- PlaneWave.FreeBoundary.GridDynamicsInterface
#print axioms FreeBoundary.extract_H_eq_gL
#print axioms FreeBoundary.potential_symm_gL
#print axioms FreeBoundary.kinetic_le_elliptic_gL
#print axioms FreeBoundary.potential_tail_le_gL
#print axioms FreeBoundary.tails_at_time_gL
#print axioms FreeBoundary.regCoeff_H_eq_grid_gL
#print axioms FreeBoundary.norm_inner_galSource_le_gL
#print axioms FreeBoundary.norm_wM_gridFlow_gridObs_le_gL

-- PlaneWave.FreeBoundary.GridDynamicsSharp
#print axioms FreeBoundary.second_moment_regCoeff_le_gL
#print axioms FreeBoundary.norm_wM_sq_gridFlow_le_gL
#print axioms FreeBoundary.shell_gridFlow_gridObs_le_gL
#print axioms FreeBoundary.grid_duality_shell_gL
#print axioms FreeBoundary.grid_observable_error_sharp_gL
#print axioms FreeBoundary.grid_observable_rate_sharp_gL

-- PlaneWave.FreeBoundary.GridDynamicsTheorem
#print axioms FreeBoundary.synth_mulCLM
#print axioms FreeBoundary.HChi_chiRefl
#print axioms FreeBoundary.grid_observable_position_sharp_gL
#print axioms FreeBoundary.grid_dyn_sharp_gL_of_propagator
#print axioms FreeBoundary.thm_grid_dyn_sharp_gL

-- PlaneWave.FreeBoundary.ProductLocalisation
#print axioms FreeBoundary.prodLocPair
#print axioms FreeBoundary.prodTorusLocPair
#print axioms FreeBoundary.free_upper_agmon_prod
#print axioms FreeBoundary.free_grid_upper_agmon_prod
#print axioms FreeBoundary.free_grid_two_sided_prod
#print axioms FreeBoundary.free_grid_exponential_prod
#print axioms FreeBoundary.free_grid_two_sidedU_prod
#print axioms FreeBoundary.free_grid_exponentialU_prod

-- PlaneWave.FreeBoundary.Complexity
#print axioms FreeBoundary.complexity_of_rate
#print axioms FreeBoundary.abs_zeroModeShift_re_le
#print axioms FreeBoundary.free_grid_complexity_prod

-- PlaneWave.FreeBoundary.FreeDynamicsGrid
#print axioms FreeBoundary.free_dyn_grid_gL

-- PlaneWave.FreeBoundary.GridDynamicsUniform
#print axioms FreeBoundary.gridConstsSharp_gL_one_le_U
#print axioms FreeBoundary.gridConstsSharp_gL_three_le_U
#print axioms FreeBoundary.gLGridA_le_U
#print axioms FreeBoundary.gridGraphNorm_gL
#print axioms FreeBoundary.norm_wPhys_gridFlow_le_gL
#print axioms FreeBoundary.norm_wPhys_gridFlow_gridObs_le_gL

-- PlaneWave.FreeBoundary.GridSecondOrderPhysical
#print axioms FreeBoundary.norm_wMul_kOp_tk_lePh
#print axioms FreeBoundary.norm_wPhys_sq_gridObs_le
#print axioms FreeBoundary.second_ellipticP
#print axioms FreeBoundary.secondConstP_le_gL
#print axioms FreeBoundary.norm_wPhys_sq_gridFlow_le_gL
#print axioms FreeBoundary.shell_gridFlow_gridObs_le_gLU

-- PlaneWave.FreeBoundary.GridSecondMomentPhysical
#print axioms FreeBoundary.layer_boundP
#print axioms FreeBoundary.norm_wTotPh_regCoeff_stateMap_le
#print axioms FreeBoundary.second_moment_regCoeff_le_gLU
#print axioms FreeBoundary.grid_duality_shell_gLU

-- PlaneWave.FreeBoundary.GridObservablePhysical
#print axioms FreeBoundary.grid_observable_error_sharp_gLU
#print axioms FreeBoundary.shell_rate_sharpP
#print axioms FreeBoundary.formAP_rate
#print axioms FreeBoundary.grid_rate_arith_sharpP

-- PlaneWave.FreeBoundary.GridDynamicsUniformTheorem
#print axioms FreeBoundary.grid_observable_rate_sharp_gLU
#print axioms FreeBoundary.grid_observable_position_sharp_gLU
#print axioms FreeBoundary.grid_dyn_sharp_gLU_of_propagator
#print axioms FreeBoundary.thm_grid_dyn_sharp_gLU
#print axioms FreeBoundary.free_dyn_grid_gLU

-- PlaneWave.FreeBoundary.ObservableMomentsUniform
#print axioms FreeBoundary.mFourierCoeff_cell
#print axioms FreeBoundary.tsum_latWeight_le
#print axioms FreeBoundary.CellDecay.hChi
#print axioms FreeBoundary.gridConstsSharp_gLU_mono
#print axioms FreeBoundary.gridConstsPosU_le_of_decay
#print axioms FreeBoundary.free_dyn_grid_gLU_decay
#print axioms FreeBoundary.free_dyn_grid_gLU_schwartz

-- PlaneWave.FreeBoundary.DomainWeakCalculus
#print axioms FreeBoundary.dirD_comm
#print axioms FreeBoundary.dirD_freeKinetic
#print axioms FreeBoundary.ibp_weight
#print axioms FreeBoundary.HasGLHamiltonian.sum
#print axioms FreeBoundary.hasGLHamiltonian_of_fourierTests
#print axioms FreeBoundary.inner_kineticTest_cutL2

-- PlaneWave.FreeBoundary.MassWeightedCutoff
#print axioms FreeBoundary.DomCutoff.toCutoff
#print axioms FreeBoundary.DomCutoff.abs_inner_cancel_le

-- PlaneWave.FreeBoundary.SingularCommutator
#print axioms FreeBoundary.dirD_pinvε
#print axioms FreeBoundary.sum_dirD_pairPotε
#print axioms FreeBoundary.abs_commWε_le
#print axioms FreeBoundary.tendsto_integral_pairPotε
#print axioms FreeBoundary.tendsto_integral_commWε
#print axioms FreeBoundary.singular_identity

-- PlaneWave.FreeBoundary.SecondCommutator
#print axioms FreeBoundary.freeId_A
#print axioms FreeBoundary.freeId_B
#print axioms FreeBoundary.freeId_comm

-- PlaneWave.FreeBoundary.CommutatorTransplant
#print axioms FreeBoundary.potential_cutL2
#print axioms FreeBoundary.inner_commH
#print axioms FreeBoundary.commT_hasGLHamiltonian

-- PlaneWave.FreeBoundary.CutStateDomain
#print axioms FreeBoundary.norm_commH_le
#print axioms FreeBoundary.cut_state_domain

-- PlaneWave.FreeBoundary.FreeDynamicsNonBO
#print axioms FreeBoundary.gridConstsSharp_gLU_mono_data
#print axioms FreeBoundary.free_dyn_grid_nbo

-- PlaneWave.FreeBoundary.CutoffScaling
#print axioms FreeBoundary.DomCutoff.scale
#print axioms FreeBoundary.DomCutoff.scale_ret
#print axioms FreeBoundary.exists_quadCutoff

-- PlaneWave.FreeBoundary.CellObservable
#print axioms FreeBoundary.continuous_cellRep_comp
#print axioms FreeBoundary.cellObs_particle
#print axioms FreeBoundary.free_dyn_grid_gLU_schwartz_cell
#print axioms FreeBoundary.free_dyn_grid_gLU_decay_cell
#print axioms FreeBoundary.free_dyn_grid_nbo_cell

-- PlaneWave.FreeBoundary.Mollification
#print axioms FreeBoundary.dirD_moll
#print axioms FreeBoundary.norm_mollL2_le
#print axioms FreeBoundary.mollL2_sub
#print axioms FreeBoundary.tendsto_mollN
#print axioms FreeBoundary.moll_dirD_eq
#print axioms FreeBoundary.moll_kin_eq
#print axioms FreeBoundary.freeKinetic_moll

-- PlaneWave.FreeBoundary.KineticRegularity
#print axioms FreeBoundary.ibp_conj
#print axioms FreeBoundary.energy_one
#print axioms FreeBoundary.energy_two
#print axioms FreeBoundary.energy_moll
#print axioms FreeBoundary.weak_kinetic_regularity

-- PlaneWave.FreeBoundary.HardyInequality
#print axioms FreeBoundary.dirD_hV
#print axioms FreeBoundary.sum_dirD_hV_ge
#print axioms FreeBoundary.hardy_smooth
#print axioms FreeBoundary.hardy_delta
#print axioms FreeBoundary.hardy_weak

-- PlaneWave.FreeBoundary.RegularityBridge
#print axioms FreeBoundary.HasWeakGrad.unique
#print axioms FreeBoundary.free_hamiltonian_regularity
#print axioms FreeBoundary.free_data_regularity
#print axioms FreeBoundary.cut_state_domain_reg
#print axioms FreeBoundary.free_dyn_grid_nbo_reg

-- PlaneWave.FreeBoundary.FreeDynamicsEndpoint
#print axioms FreeBoundary.inner_weak_kinetic
#print axioms FreeBoundary.inner_hamiltonian_im
#print axioms FreeBoundary.norm_conserved
#print axioms FreeBoundary.free_dyn_endpoint
#print axioms FreeBoundary.free_dyn_nbo_endpoint
#print axioms FreeBoundary.isGridKernel_sharp
#print axioms FreeBoundary.free_dyn_uniform
#print axioms FreeBoundary.free_dyn_nbo_uniform

-- PlaneWave.FreeBoundary.HardyNuclear
#print axioms FreeBoundary.hardy_smooth_aff
#print axioms FreeBoundary.hardy_delta_aff
#print axioms FreeBoundary.hardy_weak_aff
#print axioms FreeBoundary.hardy_nuc

-- PlaneWave.FreeBoundary.CoulombForm
#print axioms FreeBoundary.hasWeakGrad_of_contDiff
#print axioms FreeBoundary.coulomb_sub_le
#print axioms FreeBoundary.freePot_integral
#print axioms FreeBoundary.tendsto_integral_freePot

-- PlaneWave.FreeBoundary.FormApproximation
#print axioms FreeBoundary.tendsto_sigL2
#print axioms FreeBoundary.moll_freeSwap
#print axioms FreeBoundary.abs_dirD_cutN_le
#print axioms FreeBoundary.apprN_tendsto

-- PlaneWave.FreeBoundary.AgmonApproximation
#print axioms FreeBoundary.eigen_energy
#print axioms FreeBoundary.setIntegral_sq_tendsto
#print axioms FreeBoundary.freeEnergy_smul
#print axioms FreeBoundary.approx_ground
#print axioms FreeBoundary.approx_ground_agmon

-- PlaneWave.FreeBoundary.TorusApproximation
#print axioms FreeBoundary.torusEnergy_eq_form
#print axioms FreeBoundary.h2Test_sector
#print axioms FreeBoundary.approx_torus_ground
#print axioms FreeBoundary.approx_torus_agmon
#print axioms FreeBoundary.h2Form_of_eigen

-- PlaneWave.FreeBoundary.FreeEnergyEndpoint
#print axioms FreeBoundary.gLTorusGroundEnergy_ge
#print axioms FreeBoundary.free_energy_upper
#print axioms FreeBoundary.approx_torus_prod
#print axioms FreeBoundary.free_energy_endpoint
#print axioms FreeBoundary.free_energy_complexity

-- PlaneWave.FreeBoundary.NuclearPotential
#print axioms FreeBoundary.hasL2PointwisePotential_pair_nucL2
#print axioms FreeBoundary.abs_nucW_le

-- PlaneWave.FreeBoundary.NuclearRegularity
#print axioms FreeBoundary.free_hamiltonian_regularity_nuc

-- PlaneWave.FreeBoundary.NuclearSingularIdentity
#print axioms FreeBoundary.reg_identity_one_gen
#print axioms FreeBoundary.dirD_nucPotε
#print axioms FreeBoundary.abs_mul_nucDV_le
#print axioms FreeBoundary.tendsto_integral_nucPotε
#print axioms FreeBoundary.tendsto_integral_nucDV
#print axioms FreeBoundary.nuc_singular_identity

-- PlaneWave.FreeBoundary.NuclearCommutator
#print axioms FreeBoundary.freeId_comm_nuc
#print axioms FreeBoundary.inner_commHn
#print axioms FreeBoundary.commT_hasGLHamiltonian_nuc

-- PlaneWave.FreeBoundary.CutStateDomainNuclear
#print axioms FreeBoundary.norm_commHn_le
#print axioms FreeBoundary.cut_state_domain_nuc

-- PlaneWave.FreeBoundary.RegularityBridgeNuclear
#print axioms FreeBoundary.free_data_regularity_nuc
#print axioms FreeBoundary.cut_state_domain_reg_nuc

-- PlaneWave.FreeBoundary.ProductCutoff
#print axioms FreeBoundary.dirD_swap_sym
#print axioms FreeBoundary.exists_lipschitz_family
#print axioms FreeBoundary.dirD_prodChi_flat
#print axioms FreeBoundary.prodChi_isFlatNear

-- PlaneWave.FreeBoundary.ProductCutoffCancellation
#print axioms FreeBoundary.exists_prodCutoff

-- PlaneWave.FreeBoundary.ProductCutoffRegions
#print axioms FreeBoundary.prodChi_dS
#print axioms FreeBoundary.DomCutoff.scale_isFlatNear

-- PlaneWave.FreeBoundary.FreeDynamicsBO
#print axioms FreeBoundary.domConstN_mono
#print axioms FreeBoundary.free_dyn_grid_bo

-- PlaneWave.FreeBoundary.FreeDynamicsBOUniform
#print axioms FreeBoundary.prodCutoffL_derivs
#print axioms FreeBoundary.prodCutoffL_isFlatNear
#print axioms FreeBoundary.free_dyn_bo_uniform

-- PlaneWave.FreeBoundary.SpinFreeStep
#print axioms FreeBoundary.Cutoff.norm_commT_le₂
#print axioms FreeBoundary.Cutoff.sum_norm_commT_sq_le
#print axioms FreeBoundary.Cutoff.obs_cut_le
#print axioms FreeBoundary.free_dyn_torus_spin

-- PlaneWave.FreeBoundary.SpinFreeDynamicsGrid
#print axioms FreeBoundary.gridConstsSharp_gLU_nonneg
#print axioms FreeBoundary.norm_le_sq_mul_of_unit
#print axioms FreeBoundary.gridErr_smul
#print axioms FreeBoundary.free_dyn_grid_spin

-- PlaneWave.FreeBoundary.SpinFreeDynamicsEndpoint
#print axioms FreeBoundary.norm_conserved_spin
#print axioms FreeBoundary.spin_final_le
#print axioms FreeBoundary.free_dyn_nbo_spin_endpoint
#print axioms FreeBoundary.free_dyn_bo_spin_endpoint
#print axioms FreeBoundary.free_dyn_nbo_spin_uniform
#print axioms FreeBoundary.free_dyn_bo_spin_uniform

-- PlaneWave.Auxiliary.Duhamel
#print axioms PlaneWaveDynamics.duhamel_eq
#print axioms PlaneWaveDynamics.coulomb_duhamel_eq

-- PlaneWave.Auxiliary.Fold
#print axioms GridFold.sum_ephase_grid
#print axioms GridFold.fold_single
#print axioms GridFold.fold_pair
#print axioms GridFold.fold_pair_eq_zero
#print axioms GridFold.fold_pair_galerkin
#print axioms GridFold.tpoly_nuc
#print axioms GridFold.norm_nuc_coeff_le

-- PlaneWave.KineticLog.Sylvester
#print axioms KineticLog.norm_mop_le
#print axioms KineticLog.norm_sylvester_le
#print axioms KineticLog.norm_sylvester_le'
#print axioms KineticLog.hasDerivAt_phiT
#print axioms KineticLog.norm_mop_phiT_le

-- PlaneWave.KineticLog.DyadicDuhamel
#print axioms KineticLog.lmat_decomp
#print axioms KineticLog.dyadic_duhamel

-- PlaneWave.KineticLog.ExactSpectral
#print axioms KineticLog.finite_eigen_ge
#print axioms KineticLog.Hs_lower
#print axioms KineticLog.exists_exactEigen
#print axioms KineticLog.ExactEigen.inner_b_H
#print axioms KineticLog.ExactEigen.evo_b
#print axioms KineticLog.ExactEigen.inner_b_evo
#print axioms KineticLog.ExactEigen.norm_sub_proj_le
#print axioms KineticLog.ExactEigen.norm_Hs2_le

-- PlaneWave.KineticLog.SpectralTails
#print axioms KineticLog.W_tail_le
#print axioms KineticLog.zv_budget
#print axioms KineticLog.norm_tail_zv_le

-- PlaneWave.KineticLog.GalerkinConsistency
#print axioms KineticLog.galerkin_graph
#print axioms KineticLog.galerkin_delta
#print axioms KineticLog.galerkin_transfer

-- PlaneWave.KineticLog.Galerkin
#print axioms KineticLog.galerkin_coord
#print axioms KineticLog.galerkin_retained_core

-- PlaneWave.KineticLog.GalerkinEndpoint
#print axioms KineticLog.expect_sub_le
#print axioms KineticLog.kinetic_retained_galerkin
#print axioms KineticLog.thm_kinetic_log_galerkin
#print axioms KineticLog.cor_stopping_log_galerkin

-- PlaneWave.KineticLog.GalerkinSpin
#print axioms KineticLog.kinetic_retained_galerkin_spin
#print axioms KineticLog.thm_kinetic_log_galerkin_spin
#print axioms KineticLog.cor_stopping_log_galerkin_spin

-- PlaneWave.KineticLog.GridSpectral
#print axioms KineticLog.zv_budget_shift
#print axioms KineticLog.norm_tail_zv_shift_le
#print axioms KineticLog.grB_eigen
#print axioms KineticLog.grE_lower
#print axioms KineticLog.grid_flow_eigen
#print axioms KineticLog.inner_grB_flow
#print axioms KineticLog.grid_low_tail

-- PlaneWave.KineticLog.GridConsistency
#print axioms KineticLog.regCoeff_H_eq_gRes
#print axioms KineticLog.grid_cons
#print axioms KineticLog.norm_gSrc_le
#print axioms KineticLog.norm_gRes_le
#print axioms KineticLog.exact_low_reg
#print axioms KineticLog.grid_delta_raw
#print axioms KineticLog.grid_transfer_raw

-- PlaneWave.KineticLog.GridDuhamel
#print axioms KineticLog.grid_coord
#print axioms KineticLog.grid_core_pair

-- PlaneWave.KineticLog.GridShells
#print axioms KineticLog.norm_wM_regKin_shells

-- PlaneWave.KineticLog.GridTraj
#print axioms KineticLog.exact_traj_shells
#print axioms KineticLog.grid_traj_shells

-- PlaneWave.KineticLog.GridRates
#print axioms KineticLog.dRawG_le
#print axioms KineticLog.fRawG_le

-- PlaneWave.KineticLog.GridEndpoint
#print axioms KineticLog.grid_proj_term
#print axioms KineticLog.grid_kinetic_explicit
#print axioms KineticLog.thm_kinetic_log_grid
#print axioms KineticLog.cor_stopping_log_grid

-- PlaneWave.KineticLog.GridSpin
#print axioms KineticLog.thm_kinetic_log_grid_spin
#print axioms KineticLog.cor_stopping_log_grid_spin

-- PlaneWave.KineticLog.OpenExact
#print axioms KineticLog.Hs_lower_gL
#print axioms KineticLog.exists_exactEigen_gL
#print axioms KineticLog.W_tail_le_gL
#print axioms KineticLog.zv_budget_gL
#print axioms KineticLog.norm_tail_zv_gL
#print axioms KineticLog.zv_budget_shift_gL
#print axioms KineticLog.norm_tail_zv_shift_gL

-- PlaneWave.KineticLog.OpenGridSpectral
#print axioms KineticLog.grE_lower_U
#print axioms KineticLog.norm_wPhys_grVL_le
#print axioms KineticLog.grid_low_tail_U

-- PlaneWave.KineticLog.OpenConsistency
#print axioms KineticLog.regCoeff_H_eq_gRes_gL
#print axioms KineticLog.grid_cons_gL
#print axioms KineticLog.norm_gSrc_gL
#print axioms KineticLog.norm_gRes_gL
#print axioms KineticLog.exact_low_reg_gL
#print axioms KineticLog.grid_delta_raw_gL
#print axioms KineticLog.grid_transfer_raw_gL

-- PlaneWave.KineticLog.OpenDuhamel
#print axioms KineticLog.grid_coord_gL
#print axioms KineticLog.grid_core_pair_gL

-- PlaneWave.KineticLog.OpenTraj
#print axioms KineticLog.traj_tails_gL
#print axioms KineticLog.exact_traj_shells_gL
#print axioms KineticLog.datum_weight_gL
#print axioms KineticLog.grid_traj_weight_gL

-- PlaneWave.KineticLog.OpenRates
#print axioms KineticLog.dRawU_le
#print axioms KineticLog.fRawU_le
#print axioms KineticLog.datum_res_gL
#print axioms KineticLog.grid_traj_shells_gL

-- PlaneWave.KineticLog.OpenCell
#print axioms KineticLog.grid_proj_term_gL
#print axioms KineticLog.cell_kinetic_explicit
#print axioms KineticLog.T0U_scales
#print axioms KineticLog.cellK0_scales
#print axioms KineticLog.thm_cell_kinetic_log_gL

-- PlaneWave.KineticLog.OpenFree
#print axioms KineticLog.hasWeakGrad_mul
#print axioms KineticLog.inner_ibp
#print axioms KineticLog.inner_kinP_eq
#print axioms KineticLog.hasFreeWeakKinetic_massP
#print axioms KineticLog.HasFreeHamiltonian.sub
#print axioms KineticLog.norm_H_conserved

-- PlaneWave.KineticLog.OpenLocal
#print axioms KineticLog.coeff_cut_grad
#print axioms KineticLog.regKin_expect_cut
#print axioms KineticLog.free_loc_coord
#print axioms KineticLog.free_torus_kin

-- PlaneWave.KineticLog.OpenEndpoint
#print axioms KineticLog.exists_evoData_gL
#print axioms KineticLog.torus_pair_step
#print axioms KineticLog.cell_step
#print axioms KineticLog.free_kin_assemble
#print axioms KineticLog.free_kinetic_log_endpoint

-- PlaneWave.KineticLog.OpenCompat
#print axioms KineticLog.exists_kinP
#print axioms KineticLog.free_kinetic_log
#print axioms KineticLog.free_kinetic_log_nbo
#print axioms KineticLog.free_kinetic_log_bo

-- PlaneWave.KineticLog.OpenUniform
#print axioms KineticLog.free_kinetic_log_nbo_uniform
#print axioms KineticLog.free_kinetic_log_bo_uniform

-- PlaneWave.KineticLog.OpenStop
#print axioms KineticLog.secant_arith_free
#print axioms KineticLog.free_stopping_log
#print axioms KineticLog.basis_count_arith
#print axioms KineticLog.free_kinetic_log_N

-- PlaneWave.KineticLog.OpenSpin
#print axioms KineticLog.torus_pair_core
#print axioms KineticLog.free_kinetic_log_spin
#print axioms KineticLog.free_stopping_log_spin

-- PlaneWave.KineticLog.OpenSpinCompat
#print axioms KineticLog.spin_budget
#print axioms KineticLog.free_kinetic_log_nbo_spin
#print axioms KineticLog.free_kinetic_log_bo_spin
#print axioms KineticLog.free_kinetic_log_nbo_spin_uniform
#print axioms KineticLog.free_kinetic_log_bo_spin_uniform

-- PlaneWave.KineticLog.OpenFixed
#print axioms KineticLog.free_kinetic_log_at
#print axioms KineticLog.free_kinetic_log_spin_at
#print axioms KineticLog.free_stopping_log_at
#print axioms KineticLog.free_stopping_log_spin_at

-- PlaneWave.KineticLog.PeriodicUniform
#print axioms KineticLog.exists_const_forall_fin
#print axioms KineticLog.thm_kinetic_log_galerkin_all
#print axioms KineticLog.cor_stopping_log_galerkin_all
#print axioms KineticLog.kinetic_retained_galerkin_spin_all
#print axioms KineticLog.thm_kinetic_log_galerkin_spin_all
#print axioms KineticLog.cor_stopping_log_galerkin_spin_all
#print axioms KineticLog.thm_kinetic_log_grid_all
#print axioms KineticLog.cor_stopping_log_grid_all
#print axioms KineticLog.thm_kinetic_log_grid_spin_all
#print axioms KineticLog.cor_stopping_log_grid_spin_all

-- PlaneWave.KineticLog.PeriodicN
#print axioms KineticLog.basis_N_arith
#print axioms KineticLog.basis_N_arith_stop
#print axioms KineticLog.thm_kinetic_log_galerkin_N
#print axioms KineticLog.kinetic_retained_galerkin_N
#print axioms KineticLog.cor_stopping_log_galerkin_N
#print axioms KineticLog.kinetic_retained_galerkin_spin_N
#print axioms KineticLog.thm_kinetic_log_galerkin_spin_N
#print axioms KineticLog.cor_stopping_log_galerkin_spin_N
#print axioms KineticLog.thm_kinetic_log_grid_N
#print axioms KineticLog.cor_stopping_log_grid_N
#print axioms KineticLog.thm_kinetic_log_grid_spin_N
#print axioms KineticLog.cor_stopping_log_grid_spin_N

-- PlaneWave.KineticLog.PeriodicMasses
#print axioms KineticLog.PosSystem.latticeKernel_eq
#print axioms KineticLog.PosSystem.kinExpect_eq
#print axioms KineticLog.PosSystem.gridExpect_eq
#print axioms KineticLog.PosSystem.galerkinH_eq
#print axioms KineticLog.PosSystem.gridH_eq
#print axioms KineticLog.PosSystem.kernel_scaled
#print axioms KineticLog.PosSystem.exists_H
#print axioms KineticLog.Xi_evoRescale_le
#print axioms KineticLog.ode_unique
#print axioms KineticLog.PosSystem.hasDerivAt_galerkinFlow
#print axioms KineticLog.PosSystem.exists_galerkin_solution
#print axioms KineticLog.PosSystem.galerkin_solution_eq
#print axioms KineticLog.PosSystem.gridH_isSymmetric
#print axioms KineticLog.PosSystem.exists_gridPropagator
#print axioms KineticLog.PosSystem.ofCoulomb_latticeKernel
#print axioms KineticLog.PosSystem.ofCoulomb_kinExpect
#print axioms KineticLog.PosSystem.ofCoulomb_gridExpect
#print axioms KineticLog.PosSystem.ofCoulomb_galerkinH
#print axioms KineticLog.PosSystem.ofCoulomb_gridH
#print axioms KineticLog.thm_kinetic_log_galerkin_pos
#print axioms KineticLog.kinetic_retained_galerkin_pos
#print axioms KineticLog.cor_stopping_log_galerkin_pos
#print axioms KineticLog.thm_kinetic_log_grid_pos
#print axioms KineticLog.cor_stopping_log_grid_pos
#print axioms KineticLog.exists_evoData_pos
#print axioms KineticLog.thm_kinetic_log_galerkin_spin_pos
#print axioms KineticLog.cor_stopping_log_galerkin_spin_pos
#print axioms KineticLog.thm_kinetic_log_grid_spin_pos
#print axioms KineticLog.cor_stopping_log_grid_spin_pos
#print axioms KineticLog.kinetic_retained_galerkin_spin_pos
#print axioms KineticLog.thm_kinetic_log_galerkin_pos_N
#print axioms KineticLog.kinetic_retained_galerkin_pos_N
#print axioms KineticLog.cor_stopping_log_galerkin_pos_N
#print axioms KineticLog.thm_kinetic_log_grid_pos_N
#print axioms KineticLog.cor_stopping_log_grid_pos_N
#print axioms KineticLog.kinetic_retained_galerkin_spin_pos_N
#print axioms KineticLog.thm_kinetic_log_galerkin_spin_pos_N
#print axioms KineticLog.cor_stopping_log_galerkin_spin_pos_N
#print axioms KineticLog.thm_kinetic_log_grid_spin_pos_N
#print axioms KineticLog.cor_stopping_log_grid_spin_pos_N

-- PlaneWave.KineticLog.OpenVbar
#print axioms KineticLog.gLzU_mono
#print axioms KineticLog.gLmassConstU_mono
#print axioms KineticLog.gLtailMU_mono
#print axioms KineticLog.relBU_mono
#print axioms KineticLog.cellC_mono
#print axioms KineticLog.cellK0_mono
#print axioms KineticLog.locC_mono
#print axioms KineticLog.freeKinC_mono
#print axioms KineticLog.freeKinConstNBO_mono
#print axioms KineticLog.freeKinConstBO_mono
#print axioms KineticLog.free_kinetic_log_endpoint_vbar
#print axioms KineticLog.free_stopping_log_vbar
#print axioms KineticLog.free_kinetic_log_N_vbar
#print axioms KineticLog.free_kinetic_log_spin_vbar
#print axioms KineticLog.free_stopping_log_spin_vbar
#print axioms KineticLog.free_kinetic_log_nbo_vbar
#print axioms KineticLog.free_kinetic_log_bo_vbar
#print axioms KineticLog.free_kinetic_log_nbo_spin_vbar
#print axioms KineticLog.free_kinetic_log_bo_spin_vbar
#print axioms KineticLog.free_kinetic_log_vbar
#print axioms KineticLog.free_kinetic_log_at_vbar
#print axioms KineticLog.free_kinetic_log_spin_at_vbar
#print axioms KineticLog.free_stopping_log_at_vbar
#print axioms KineticLog.free_stopping_log_spin_at_vbar
#print axioms KineticLog.free_kinetic_log_nbo_uniform_vbar
#print axioms KineticLog.free_kinetic_log_bo_uniform_vbar
#print axioms KineticLog.free_kinetic_log_nbo_spin_uniform_vbar
#print axioms KineticLog.free_kinetic_log_bo_spin_uniform_vbar

-- PlaneWave.KineticLog.OpenZeroMode
#print axioms KineticLog.gLFourierPotentialZ_eq
#print axioms KineticLog.hasGLHamiltonianZ_iff
#print axioms KineticLog.budget_zero_mode
#print axioms KineticLog.gridTerm_update
#print axioms KineticLog.Hgrid_update
#print axioms KineticLog.gridZeroWeight_im
#print axioms KineticLog.propagator_phase
#print axioms KineticLog.cell_phase
#print axioms KineticLog.exists_gLPropagatorZ
#print axioms KineticLog.cell_phase_eq
#print axioms KineticLog.IsGridKernelZ.zero
#print axioms KineticLog.IsGridKernelZ.zeroed
#print axioms KineticLog.IsGridKernelZ.ofIsGridKernel
#print axioms KineticLog.isGridKernelZ_sharp
#print axioms KineticLog.regExpect_phase
#print axioms KineticLog.grid_phase
#print axioms KineticLog.gridZero_eq_zeroModeShift
#print axioms KineticLog.budget_zero_mode_spin
#print axioms KineticLog.free_kinetic_log_phys_endpoint
#print axioms KineticLog.free_stopping_log_phys_endpoint
#print axioms KineticLog.free_kinetic_log_spin_phys_endpoint
#print axioms KineticLog.free_stopping_log_spin_phys_endpoint
#print axioms KineticLog.free_kinetic_log_N_phys_endpoint
#print axioms KineticLog.free_kinetic_log_phys
#print axioms KineticLog.free_kinetic_log_phys_at
#print axioms KineticLog.free_kinetic_log_spin_phys_at
#print axioms KineticLog.free_stopping_log_phys_at
#print axioms KineticLog.free_stopping_log_spin_phys_at
#print axioms KineticLog.free_kinetic_log_nbo_phys
#print axioms KineticLog.free_kinetic_log_bo_phys
#print axioms KineticLog.free_kinetic_log_nbo_spin_phys
#print axioms KineticLog.free_kinetic_log_bo_spin_phys
#print axioms KineticLog.free_kinetic_log_nbo_uniform_phys
#print axioms KineticLog.free_kinetic_log_bo_uniform_phys
#print axioms KineticLog.free_kinetic_log_nbo_spin_uniform_phys
#print axioms KineticLog.free_kinetic_log_bo_spin_uniform_phys

-- PlaneWave.FreeBoundary.EnergyVbar
#print axioms FreeBoundary.EbigU_mono
#print axioms FreeBoundary.CgridU_mono
#print axioms FreeBoundary.gLCubicConstU_mono
#print axioms FreeBoundary.gLKcubU_mono
#print axioms FreeBoundary.gLKThresholdU_mono
#print axioms FreeBoundary.gLErrorConstU_mono
#print axioms FreeBoundary.freeUpperBudget_mono
#print axioms FreeBoundary.gLSectorKernelGridErrorU_vbar
#print axioms FreeBoundary.gLSectorGridErrorU_vbar
#print axioms FreeBoundary.free_energy_upper_vbar
#print axioms FreeBoundary.free_energy_endpoint_vbar
#print axioms FreeBoundary.free_energy_complexity_vbar
#print axioms FreeBoundary.free_grid_complexity_prod_vbar
#print axioms FreeBoundary.gLTorusGroundEnergy_ge_vbar
#print axioms FreeBoundary.free_grid_two_sidedU_vbar
#print axioms FreeBoundary.free_grid_exponentialU_vbar
#print axioms FreeBoundary.free_grid_two_sidedU_prod_vbar
#print axioms FreeBoundary.free_grid_exponentialU_prod_vbar

-- PlaneWave.FreeBoundary.DynamicsVbar
#print axioms FreeBoundary.flow2_mono'
#print axioms FreeBoundary.sigmaU_mono
#print axioms FreeBoundary.gridPhiU_mono_V
#print axioms FreeBoundary.gridConstsSharp_gLU_mono_V
#print axioms FreeBoundary.dynConst_mono
#print axioms FreeBoundary.freeDynConst_mono
#print axioms FreeBoundary.freeDynConstNBO_mono
#print axioms FreeBoundary.freeDynConstBO_mono
#print axioms FreeBoundary.freeDynConstSpinNBO_mono
#print axioms FreeBoundary.freeDynConstSpinBO_mono
#print axioms FreeBoundary.free_dyn_endpoint_vbar
#print axioms FreeBoundary.free_dyn_nbo_endpoint_vbar
#print axioms FreeBoundary.free_dyn_grid_bo_vbar
#print axioms FreeBoundary.free_dyn_uniform_vbar
#print axioms FreeBoundary.free_dyn_nbo_uniform_vbar
#print axioms FreeBoundary.free_dyn_bo_uniform_vbar
#print axioms FreeBoundary.free_dyn_nbo_spin_endpoint_vbar
#print axioms FreeBoundary.free_dyn_bo_spin_endpoint_vbar
#print axioms FreeBoundary.free_dyn_nbo_spin_uniform_vbar
#print axioms FreeBoundary.free_dyn_bo_spin_uniform_vbar

-- PlaneWave.FreeBoundary.DynamicsZeroMode
#print axioms FreeBoundary.Hpos_update
#print axioms FreeBoundary.Hpos_isSymmetric
#print axioms FreeBoundary.posProp_phase
#print axioms FreeBoundary.posProp_phase_zeroMode
#print axioms FreeBoundary.exists_posPropagatorZ
#print axioms FreeBoundary.budget_zero_mode_each
#print axioms FreeBoundary.cell_unphase
#print axioms FreeBoundary.exists_gLPropagatorZ'
#print axioms FreeBoundary.free_dyn_torus_phys
#print axioms FreeBoundary.free_dyn_torus_spin_phys
#print axioms FreeBoundary.free_dyn_endpoint_phys
#print axioms FreeBoundary.free_dyn_nbo_endpoint_phys
#print axioms FreeBoundary.free_dyn_grid_bo_phys
#print axioms FreeBoundary.free_dyn_uniform_phys
#print axioms FreeBoundary.free_dyn_nbo_uniform_phys
#print axioms FreeBoundary.free_dyn_bo_uniform_phys
#print axioms FreeBoundary.free_dyn_nbo_spin_endpoint_phys
#print axioms FreeBoundary.free_dyn_bo_spin_endpoint_phys
#print axioms FreeBoundary.free_dyn_nbo_spin_uniform_phys
#print axioms FreeBoundary.free_dyn_bo_spin_uniform_phys
