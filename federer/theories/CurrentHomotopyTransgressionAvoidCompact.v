(** Federer (1969), 4.1.9, p. 363: the smooth
    homotopy form vanishes where the entire original path
    avoids the original target support. This supporting
    locality law retains arbitrary source domains and follows
    directly from the sealed literal time-integral law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing CurrentSpaces CurrentCoefficientNorms
  CurrentCartesianDomain CurrentCartesianVectorProduct SmoothCompactSet SmoothFunctionSupport
  SmoothFormPullbackSealed SmoothFormPullbackSupport CurrentSegmentCompactSet CurrentHomotopyUP
  CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyTransgressionUP CurrentHomotopyTransgressionSealed
  CurrentHomotopyAvoidCompact ConvexMetricSegment RealMetricBackground LebesgueScalarMeasure
  MeasureIntegralUniqueness MeasureSubsetIntegral RealSubsetIntegralGraph SummableRealFunctionUP LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionAvoidCompact.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
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
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation fv := (@current_smooth_value R h2 nu V hV (1+j)).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation Pull := (@SmoothFormPullback.operator R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2).
Local Notation pv := (@current_smooth_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation KH := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Local Notation Integrand := (@current_homotopy_transgression_integrand R h2 n nu j A U V f g h hHomotopy).
Local Notation I := (`[0,1]:set (real_line_metric R)).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hInterval).
Local Notation KTime := (@current_segment_compact_set R 1%N AT u v hSegment).
Variable K:smooth_compact_set hNY V.
Local Notation Avoid := (@current_homotopy_avoid_compact R n nu A U V f g h geometry K).

(** Source for [current_homotopy_transgression_avoids_compact]:
    a smooth form supported in the original compact K has
    zero homotopy form on the whole-path avoidance locus,
    supporting the original current restatement in Federer
    4.1.9, p. 363. No properness or compact support
    of the source is required for this locality law. *)
Theorem current_homotopy_transgression_avoids_compact (psi:F):
  @smooth_function_support R Y (A_m Y R^o (1+j)) NY hNY V F fv psi `<=` smooth_compact_carrier K->
  forall x,Avoid x->ev (KH psi) x=0.
Proof.
move=>hPsi x [hx hAvoid];apply:pairing_ext=>eta.
have hZero t (ht:I t):Integrand psi x eta t=0.
  pose a:=@metric_segment_point R (R_n R 1%N) u v t.
  have hTime:=@current_segment_point_in_compact R 1%N AT u v hSegment t ht.
  have hPoint:AU (euclidean_block_join (a,x)).
    change (AT (@euclidean_block_split R 1%N n (euclidean_block_join (a,x))).1 /\
      U (@euclidean_block_split R 1%N n (euclidean_block_join (a,x))).2).
    rewrite euclidean_block_joinK;split;last exact:hx.
    exact:(@hSegment t ht).
  have hPull:=@smooth_form_pullback_zero_off_compact R h2 (1+n)%N nu (1+j) AU V hAU hV
    h image hHomotopy.2 psi K hPsi (euclidean_block_join (a,x)) hPoint (@hAvoid a hTime).
  rewrite /current_homotopy_transgression_integrand hPull.
  exact:(bil0r (@pairing_bilinear R (R_n R (1+n)%N) R^o (1+j)) _).
have hTotal:=@real_total_zero_integral R (real_line_metric R) (@lebesgue_scalar_measure R)
  (@lebesgue_scalar_is_measure R).
have hSubset:=(@real_subset_integral_total R (real_line_metric R) (@lebesgue_scalar_measure R) I
  (Integrand psi x eta) (fun _=>0) (0:R)%:E (fun t ht=>esym (hZero t ht)) (fun _ _=>erefl)).2 hTotal.
have hOriginal:=@CurrentHomotopyTransgression.laws R h2 n nu j A U V f g h hHomotopy psi x hx eta.
have hEqual:=EFin_inj (measure_integral_unique hOriginal hSubset).
exact:(eq_trans hEqual (esym (bil0r (@pairing_bilinear R X R^o j) eta))).
Qed.
End CurrentHomotopyTransgressionAvoidCompact.
