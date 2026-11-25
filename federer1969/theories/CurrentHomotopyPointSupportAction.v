(** Federer (1969), 4.1.9, p. 363: apply the original
    time-slice integral to currents supported at a given point.
    This includes the point multivector current and its boundary.
    Actual compact replacements agree near the whole original
    product support; the smooth form is evaluated only through
    the unique compact-current extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentSpaces CurrentSupportGeometry CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianSliceSealed CurrentCartesianProductAction CurrentCartesianSupportUpper
  SmoothCompactSet CurrentCompactSmoothValue CurrentCompactSmoothAgreement CurrentCompactSmoothAlgebra
  CurrentCompactPushforwardSmooth CurrentPushforwardNormality CurrentPushforwardSealed
  SmoothFormPullbackSealed CurrentSegmentCompactSet OrientedSegmentCurrentSupport
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyCylinder
  CurrentHomotopyProductSupport CurrentDeformationChainSealed CurrentDeformationChainPushforward
  CurrentDeformationChainCompact CurrentHomotopyTransgressionSealed CurrentHomotopyTransgressionLocalTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyPointSupportAction.
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
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation Pull := (@SmoothFormPullback.operator R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_homotopy_time_segment_domain R A hInterval).
Local Notation S := (@current_homotopy_time_segment R A hInterval h2).
Local Notation KTime := (@current_segment_compact_set R 1%N AT u v hSegment).
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Variable x:X.
Hypothesis hx:U x.
Variable T:@current_space R h2 n U hU j.
Hypothesis hPointSupport:@current_support R h2 n U hU j T `<=` [set x].
Local Notation KPoint := (@smooth_compact_singleton R X NX hNX U x hx).
Hypothesis hCompactT:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU j T).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU S T).
Local Notation hCompactProduct := (@current_homotopy_compact_product R h2 n nu j A U V f g h hHomotopy T hCompactT).

(** Source for [current_homotopy_point_support_product_action]:
    the extended original segment-product action on h#psi
    is T applied to the smooth homotopy form, supporting
    the point-current deduction in Federer 4.1.9, p. 363.
    T may be any current supported in {x}, including a
    derivative of the point current or the zero current. *)
Theorem current_homotopy_point_support_product_action (psi:F):
  @current_compact_smooth_value R h2 (1+n)%N (1+j) AU hAU product hCompactProduct (Pull psi)=
    @current_compact_smooth_value R h2 n j U hU T hCompactT (K psi).
Proof.
have[Q [W [O [hW [hWx [hWU [hO [hKO [hOAU [hQ hSlice]]]]]]]]]]:=
  @current_homotopy_transgression_local_test R h2 n nu j A U V f g h hHomotopy x hx.
have hProductSupport z:@current_support R h2 (1+n)%N AU hAU (1+j) product z->O z.
  move=>hz.
  have hSides:=@current_cartesian_support_upper R h2 1%N n 1%N j AT U hAT hU S T z hz.
  have hTime:=@oriented_segment_current_support R h2 1%N AT hAT u v hSegment (p z) hSides.1.
  have hSpatial:q z=x:=@hPointSupport (q z) hSides.2.
  have hJoined:=@hKO (p z) hTime.
  rewrite -hSpatial in hJoined.
  have hJoin:euclidean_block_join (p z,q z)=z:=@euclidean_block_splitK R 1%N n z.
  by rewrite hJoin in hJoined.
have hProductValue:=@current_compact_near_support_smooth_value R h2 (1+n)%N (1+j) AU hAU
  product hCompactProduct (Pull psi) (Q psi) O hO hProductSupport (fun z hz=>esym (@hQ psi z hz)).
have hTW:forall y,@current_support R h2 n U hU j T y->W y.
  move=>y hy;have hEqual:y=x:=@hPointSupport y hy.
  by rewrite hEqual.
have hTValue:=@current_compact_near_support_smooth_value R h2 n j U hU T hCompactT
  (K psi) (@CartesianSlice.value R h2 1%N n 1%N j AT U hAT hU S (Q psi)) W hW hTW
  (fun y hy=>esym (@hSlice psi y hy)).
exact:(eq_trans hProductValue (eq_trans
  (@current_cartesian_product_action R h2 1%N n 1%N j AT U hAT hU S T (Q psi)) (esym hTValue))).
Qed.

(** Source for [current_deformation_chain_point_support_smooth_action]:
    the actual original deformation chain of a point-supported
    current acts on a smooth form by T(K psi), supporting
    Federer 4.1.9, p. 363. The compactness and all
    test replacements are proved; no ordinary test-dual action
    on a noncompact form is introduced. *)
Theorem current_deformation_chain_point_support_smooth_action
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T) (psi:F):
  @current_compact_smooth_value R h2 nu (1+j) V hV
    (@CurrentDeformationChain.value R h2 n nu j A U V f g h hHomotopy T hProper)
    (@current_deformation_chain_compact R h2 n nu j A U V f g h hHomotopy T hCompactT hProper) psi=
  @current_compact_smooth_value R h2 n j U hU T hCompactT (K psi).
Proof.
pose hP:=@current_homotopy_product_proper R h2 n nu j A U V f g h geometry T hProper.
pose pushed:=@CurrentPushforward.value R h2 (1+n)%N nu (1+j) AU V hAU hV product h image hHomotopy.2 hP.
pose hCompactPushed:=@current_pushforward_compact_support R h2 (1+n)%N nu AU V hAU hV h image
  hHomotopy.2 (1+j) product hP hCompactProduct.
have hEqual:=@current_deformation_chain_pushforward R h2 n nu j A U V f g h hHomotopy T hProper.
have hExtension:=@current_compact_smooth_congruence R h2 nu (1+j) V hV
  (@CurrentDeformationChain.value R h2 n nu j A U V f g h hHomotopy T hProper) pushed
  (@current_deformation_chain_compact R h2 n nu j A U V f g h hHomotopy T hCompactT hProper)
  hCompactPushed hEqual.
have hValue:=@current_compact_pushforward_smooth_value R h2 (1+n)%N nu (1+j) AU V hAU hV h image
  hHomotopy.2 product hP hCompactProduct psi.
exact:(eq_trans (congr1 (fun L:Hom F R^o=>L psi) hExtension)
  (eq_trans hValue (current_homotopy_point_support_product_action psi))).
Qed.
End CurrentHomotopyPointSupportAction.
