(** Federer (1969), 4.1.9, p. 363: the smooth homotopy
    form has an actual compact-test representative near each
    source point, obtained by slicing one admissible compact
    replacement of the original smooth pullback. This links
    the current and form equations without a false compactness
    claim for the global homotopy form. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing CurrentSpaces
  CurrentCartesianDomain CurrentCartesianVectorProduct CurrentCartesianSliceSealed CurrentCartesianLocalCutoff
  SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackSealed
  CurrentSegmentCompactSet CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentHomotopyTransgressionUP CurrentHomotopyTransgressionSealed OrientedSegmentSliceIntegral ConvexMetricSegment
  RealMetricBackground LebesgueScalarMeasure MeasureSubsetIntegral MeasureIntegralUniqueness
  SummableRealFunctionUP RealSubsetIntegralAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionLocalTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
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
Local Notation DC := (@current_test_space R h2 (1+n)%N AU hAU (1+j)).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation Pull := (@SmoothFormPullback.operator R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2).
Local Notation pv := (@current_smooth_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation tv := (@current_test_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation bv := (@current_test_value R h2 n U hU j).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hInterval).
Local Notation KTime := (@current_segment_compact_set R 1%N AT u v hSegment).
Local Notation S := (@current_homotopy_time_segment R A hInterval h2).
Local Notation Slice := (@CartesianSlice.value R h2 1%N n 1%N j AT U hAT hU S).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Local Notation velocity := (exterior_first_inclusion (R_n R 1%N) (v-u)).
Local Notation Product := (@current_cartesian_vector_product R 1%N n 1%N j).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [current_homotopy_transgression_local_test]:
    one actual compact replacement of every smooth pullback
    is admissible near the whole original time segment at x,
    and its actual slice agrees with the opaque smooth
    homotopy form near x, supporting Federer 4.1.9, p. 363.
    This includes noncompact original smooth target forms. *)
Theorem current_homotopy_transgression_local_test x (hx:U x):
  exists (Q:Hom F DC) (W:set X) (O:set Z),
    @open (real_norm_metric_space hNX) W /\ W x /\ W `<=` U /\
    @open (real_norm_metric_space hNZ) O /\
    (forall a,smooth_compact_carrier KTime a->O (euclidean_block_join (a,x))) /\
    O `<=` AU /\
    (forall psi z,O z->tv (Q psi) z=pv (Pull psi) z) /\
    forall psi y,W y->bv (Slice (Q psi)) y=ev (K psi) y.
Proof.
have[C [W [O [hW [hWx [hWU [hO [hKO [hOAU [hC hStrip]]]]]]]]]]:=
  @current_cartesian_local_cutoff_strong R h2 1%N n (1+j) AT U hAT hU KTime x hx.
pose Q:=hom_comp C Pull.
exists Q,W,O;split=>//;split=>//;split=>//;split=>//;split=>//;split=>//;split.
- move=>psi z hz;exact:(@hC (Pull psi) z hz).
- move=>psi y hy;apply:pairing_ext=>eta.
  have hSlice:=@oriented_segment_slice_integral R h2 1%N n j AT U hAT hU u v hSegment
    (Q psi) y (hWU y hy) eta.
  have hPoint t:I t->
      pairing (Product velocity eta) (tv (Q psi) (euclidean_block_join (metric_segment_point u v t,y)))=
      @current_homotopy_transgression_integrand R h2 n nu j A U V f g h hHomotopy psi y eta t.
    move=>ht.
    exact:(congr1 (pairing (Product velocity eta))
      (@hStrip (Pull psi) (metric_segment_point u v t) y
        (@current_segment_point_in_compact R 1%N AT u v hSegment t ht) hy)).
  have hIntegral:=@real_subset_integral_agreement R (real_line_metric R) (@lebesgue_scalar_measure R)
    I _ _ _ hPoint hSlice.
  have hOriginal:=@CurrentHomotopyTransgression.laws R h2 n nu j A U V f g h hHomotopy psi y (hWU y hy) eta.
  have hEqual:=measure_integral_unique hIntegral hOriginal.
  by injection hEqual.
Qed.
End CurrentHomotopyTransgressionLocalTest.
