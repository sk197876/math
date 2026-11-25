(** Federer (1969), 4.1.12, p. 369: the
    common coordinate test has value v-u
    on each original positive segment [u,v].
    Apply the original segment integral of
    4.1.8, p. 362, and
    the earlier integral of a constant. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology normedtype lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCoordinateForms EuclideanScalarCoordinateMaps
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing OneFormIdentification ExteriorFirstPairingTuple
  CurrentSpaces OrientedSegmentCurrentUP OrientedSegmentCurrentSealed ScalarSegmentCoordinateValues
  ScalarCurrentIntervalCompact SmoothCompactSet ConvexMetricSegment RealMetricBackground
  LebesgueScalarMeasure MeasureUP BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  PartialZeroExtension MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureSubsetIntegral MeasureSubsetConstantIntegral
  RealSubsetIntegralAgreement SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarSegmentCalibration.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (@current_test_space R h2 1%N Full hFull 1%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 1%N).
Local Notation dx := (@euclidean_coordinate_form R 1%N ord0).

(** Source for [scalar_segment_calibration_value]: an
    actual original test equal to DX
    on the common [a,b] has value
    d-c on every positively oriented
    [c,d] inside it. This supports the
    exact mass equality of Federer
    4.1.12, p. 369; degenerate
    segments are retained. *)
Theorem scalar_segment_calibration_value (a b c d:R) (phi:DT):
  a<=c->c<=d->d<=b->
  (forall x,smooth_compact_carrier (scalar_current_compact_interval R a b) x->value phi x=dx)->
  @current_value R h2 1%N Full hFull 1%N
    (@OrientedSegmentCurrent.value R h2 1%N Full hFull
      (euclidean_one_embed c) (euclidean_one_embed d) (@scalar_segment_full_domain R c d)) phi=d-c.
Proof.
move=>hac hcd hdb hCalibration.
pose velocity:=exterior_first_inclusion X (euclidean_one_embed d-euclidean_one_embed c).
pose f t:=pairing velocity (value phi (metric_segment_point (euclidean_one_embed c) (euclidean_one_embed d) t)).
have hPoint t:(`[0,1]:set R) t->f t=d-c.
  move=>ht.
  have hBounds:0<=t<=1 by move:ht;rewrite /mkset in_itv /=.
  have[h0 h1]:=andP hBounds.
  have hLength:0<=d-c by rewrite subr_ge0.
  have hLower:0<=(d-c)*t:=mulr_ge0 hLength h0.
  have hUpper:(d-c)*t<=d-c.
    have h:=ler_wpM2l hLength h1;by rewrite mulr1 in h.
  have hIn:smooth_compact_carrier (scalar_current_compact_interval R a b)
      (metric_segment_point (euclidean_one_embed c) (euclidean_one_embed d) t).
    rewrite scalar_current_compact_interval_carrier /= scalar_segment_parameter_value euclidean_one_embedK.
    apply/andP;split;lra.
  rewrite /f (hCalibration _ hIn) /velocity exterior_first_pairing_tuple.
  by rewrite /euclidean_coordinate_form one_formE /euclidean_scalar_coordinate_map /=
    /euclidean_one_embed !ffunE.
have hMeas:measure_measurable (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R)).
  apply:(@borel_regular_borel_measurable R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact:closed_borel_set (@segment_closed_real R 0 1).
have hNonnegative:(0<=(d-c)%:E)%E by rewrite lee_fin subr_ge0.
have hConstant:=@measure_nonnegative_constant_subset_integral R (real_line_metric R)
  (@lebesgue_scalar_measure R) `[0,1] (d-c)%:E (lebesgue_scalar_is_measure R) hMeas hNonnegative.
rewrite lebesgue_scalar_segment ?ler01 // subr0 mule1 in hConstant.
have hRealConstant:is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun _:real_line_metric R=>d-c)) (d-c)%:E.
  apply:(@measure_integral_graph_equivalent R (real_line_metric R) (@lebesgue_scalar_measure R)
    _ _ _ _ hConstant)=>t z.
  by rewrite !partial_function_zero_extension_graph real_total_integrand_graph.
have hActual:=@real_subset_integral_agreement R (real_line_metric R) (@lebesgue_scalar_measure R)
  `[0,1] (fun _=>d-c) f (d-c)%:E (fun t ht=>esym (hPoint t ht)) hRealConstant.
have hOriginal:=@OrientedSegmentCurrent.laws R h2 1%N Full hFull
  (euclidean_one_embed c) (euclidean_one_embed d) (@scalar_segment_full_domain R c d) phi.
exact:EFin_inj (measure_integral_unique hOriginal hActual).
Qed.
End ScalarSegmentCalibration.
