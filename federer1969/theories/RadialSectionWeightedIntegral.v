(** Federer (1969), 3.2.36, p. 273: actual intrinsic-volume
    weights multiply the normalized radial section integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanBallVolume WeightedRadialSectionIntegral RealOpenIntervals
  LebesgueScalarMeasure ExtendedRealOrderTopology PartialFunctionBasic PartialZeroExtension
  SummableRealFunctionUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence SubsetFiniteNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_section_weighted_integral]: the individual
    finite-sum radius integrals in Federer 3.2.36, p. 273.
    Any nonnegative extended constant multiplies the proved normalized
    section integral. Nonnegativity is required only on the original
    positive interval; zero second degree and the line sphere are
    included. Exact total-graph transfer precedes actual scaling. *)
Lemma radial_section_weighted_integral (R:realType) m k (r:R) (c: \bar R):
  (0<m)%N ->(0<r)%R ->0<=c ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun s:R=>(c*(m%:R*euclidean_unit_ball_volume R m*
      euclidean_unit_ball_volume R k*s^+(m-1)*Num.sqrt (r^+2-s^+2)^+k)%R%:E
        :extended_real_line R)))
    (c*(euclidean_unit_ball_volume R (m+k)*r^+(m+k))%R%:E).
Proof.
move=>hm hr hc.
pose v:=fun s:R=>(m%:R*euclidean_unit_ball_volume R m*
  euclidean_unit_ball_volume R k*s^+(m-1)*Num.sqrt (r^+2-s^+2)^+k)%R.
have hBase:=@weighted_radial_section_integral R m k r hm hr.
have hTotal:is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun s:R=>((v s)%:E:extended_real_line R)))
    (euclidean_unit_ball_volume R (m+k)*r^+(m+k))%R%:E.
  apply:(measure_integral_graph_equivalent _ hBase)=>s z.
  case:(pselect (real_open_interval 0 r s))=>hs.
  - rewrite !(partial_function_zero_extension_on _ _ _ hs) real_total_integrand_graph; reflexivity.
  - by rewrite !(partial_function_zero_extension_off _ _ _ hs).
have hPositive s:real_open_interval 0 r s ->0<=(v s)%:E.
  move=>[hs _]; rewrite lee_fin /v; apply:mulr_ge0.
  - apply:mulr_ge0; last by apply:exprn_ge0; exact:ltW hs.
    apply:mulr_ge0; last exact:ltW (euclidean_unit_ball_volumeE R k).2.
    apply:mulr_ge0; [exact:ler0n|exact:ltW (euclidean_unit_ball_volumeE R m).2].
  - apply:exprn_ge0; exact:sqrtr_ge0.
exact:(@subset_nonnegative_extended_scale_integral R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (real_open_interval 0 r)
  (fun s:R=>((v s)%:E:extended_real_line R)) _ c hPositive hc hTotal).
Qed.
