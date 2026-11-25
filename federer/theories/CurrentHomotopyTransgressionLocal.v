(** Federer (1969), 4.1.9, p. 363: the literal time
    integral defining the homotopy form is locally the actual
    smooth Cartesian slice of a compact replacement. The
    compact first factor is the original unit time segment.
    No properness or support hypothesis is imposed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing CurrentSpaces
  CurrentCartesianDomain CurrentCartesianVectorProduct CurrentCartesianSliceSealed CurrentCartesianLocalCutoff
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackSealed
  CurrentSegmentCompactSet CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentHomotopyTransgressionUP OrientedSegmentSliceIntegral ConvexMetricSegment
  RealMetricBackground LebesgueScalarMeasure PartialFunctionUP PartialZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral RealSubsetIntegralAgreement SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionLocal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation Pull := (@SmoothFormPullback.operator R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2).
Local Notation pv := (@current_smooth_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation tv := (@current_test_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hInterval).
Local Notation KTime := (@current_segment_compact_set R 1%N AT u v hSegment).
Local Notation S := (@current_homotopy_time_segment R A hInterval h2).
Local Notation Slice := (@CartesianSlice.value R h2 1%N n 1%N j AT U hAT hU S).
Local Notation Inc := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU j)).
Local Notation velocity := (exterior_first_inclusion (R_n R 1%N) (v-u)).
Local Notation Product := (@current_cartesian_vector_product R 1%N n 1%N j).
Local Notation I := (`[0,1]:set (real_line_metric R)).
Local Notation Integrand := (@current_homotopy_transgression_integrand R h2 n nu j A U V f g h hHomotopy).

(** Source for [current_homotopy_transgression_local]: one
    actual linear smooth-form operator realizes the original
    homotopy integral on a neighbourhood of any source point,
    supporting Federer 4.1.9, p. 363. The original
    whole time segment is retained in the integral; the
    compact replacement is only an existence proof. *)
Theorem current_homotopy_transgression_local x (hx:U x):
  exists (L:Hom F E) (W:set X),
    @open (real_norm_metric_space hNX) W /\ W x /\ W `<=` U /\
    forall psi y,W y->forall eta:exterior_power X j,
      is_measure_subset_integral (@lebesgue_scalar_measure R) I
        (real_total_integrand (Integrand psi y eta))
        (pairing eta (ev (L psi) y))%:E.
Proof.
have[Q [W [hW [hWx [hWU hQ]]]]]:=
  @current_cartesian_local_cutoff R h2 1%N n (1+j) AT U hAT hU KTime x hx.
pose L:=hom_comp Inc (hom_comp Slice (hom_comp Q Pull)).
exists L,W;split=>//;split=>//;split=>// psi y hy eta.
have hSlice:=@oriented_segment_slice_integral R h2 1%N n j AT U hAT hU u v hSegment
  (Q (Pull psi)) y (hWU y hy) eta.
change (is_measure_subset_integral (@lebesgue_scalar_measure R) I
  (real_total_integrand (fun t=>pairing (Product velocity eta)
    (tv (Q (Pull psi)) (euclidean_block_join (metric_segment_point u v t,y)))))
  (pairing eta (ev (L psi) y))%:E) in hSlice.
have hPoint t:I t->
    pairing (Product velocity eta)
      (tv (Q (Pull psi)) (euclidean_block_join (metric_segment_point u v t,y)))=
    Integrand psi y eta t.
  move=>ht.
  have hTime:=@current_segment_point_in_compact R 1%N AT u v hSegment t ht.
  by rewrite (@hQ (Pull psi) (metric_segment_point u v t) y hTime hy).
exact:(@real_subset_integral_agreement R (real_line_metric R) (@lebesgue_scalar_measure R)
  I _ _ _ hPoint hSlice).
Qed.
End CurrentHomotopyTransgressionLocal.
