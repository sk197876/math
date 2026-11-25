(** Actual-space endpoint regressions for Federer (1969), 4.1.13,
    pp. 369–370. Apply the final original-domain theorem to a
    nonzero normal interval under identity maps, a translated
    nonzero point current in R^0, and the zero current with empty
    original source and target. The compact index is the original
    segment hull in every case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanOneNormDifferential
  EuclideanHomOperator OperatorNormSealed CurrentDomain CurrentSpaces
  CurrentEvaluation CurrentBoundary CurrentDirac DiracCurrentBounds
  CurrentDiracRadonRepresentation CurrentIntegrationCriterion
  NormalisedCurrentSealed NormalisedDistributionRepresentationUP
  DistributionIntegrationRepresentationUP NormalCurrentsUP NormalCurrentLinear
  CurrentSegmentMapUP ScalarSegmentCoordinateValues OrientedSegmentCurrentSealed
  OrientedSegmentNormal OrientedSegmentMass CurrentMassSealed CurrentMassBasic
  CurrentCompactPushforwardAlgebra CurrentCompactElementaryPushforwards
  CurrentMapDifferential CurrentOpenIdentitySmooth CurrentAffineSegmentHull
  CurrentFlatAffineImages CurrentFlatNorm CurrentFlatDualSeminormBasic
  CurrentSupportExtensionality
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  SummableRealFunctionUP LatticeL1ApproximationLaws PointMassIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_endpoint_zero_lower_value]: the zero-weight
    endpoint of the original variation integrals in Federer
    4.1.13, p. 369, using the zero integral of 2.4.4, p. 82.
    Infinite total variation is allowed. This supports the actual
    identity-map and empty-source regressions below. *)
Local Lemma affine_endpoint_zero_lower_value (R:realType) (A:choiceType)
    (mu:set A->\bar R) (hm:is_measure mu):
  measure_lower_integral mu (real_total_integrand (fun _:A=>(0:R)))=0%E.
Proof.
have h:=@real_total_zero_integral R A mu hm.
exact:(measure_lower_integral_unique
  (measure_lower_integral_specification mu
    (real_total_integrand (fun _:A=>(0:R)))) h.2.2).
Qed.

Section AffineCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  @norm_full_domain_interior R X NX x).
Local Notation one := (@euclidean_one_embed R 1).
Local Notation segmentDomain := (@scalar_segment_full_domain R 0 1).
Local Notation interval := (@OrientedSegmentCurrent.value R h2 1%N
  Full hFull (@euclidean_one_embed R 0) one segmentDomain).
Local Notation hInterval := (@oriented_segment_current_normal R h2 1%N
  Full hFull (@euclidean_one_embed R 0) one segmentDomain).
Local Notation Id := (fun x:X=>x).
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation hId := (@current_open_identity_smooth R 1%N Full hFull).
Local Notation hHull := (fun (y:X)
  (_:@current_affine_segment_hull R h2 1%N 1%N 1%N Full hFull
    Id Id interval y)=>Logic.I).
Local Notation K := (@current_affine_image_compact R h2 1%N 1%N 1%N
  Full Full hFull Id Id hId hId interval hInterval hHull).
Local Notation P := (@current_compact_map_pushforward R h2 1%N 1%N
  Full Full hFull hFull Id hImage hId 1%N interval hInterval.2).
Local Notation UT := (current_domain R 1%N Full).
Local Notation boundary := (@current_boundary R h2 1%N 0%N
  Full hFull interval).
Local Notation mu := (@NormalisedCurrent.measure R h2 1%N 1%N
  Full hFull interval hInterval.1.1).
Local Notation muB := (@NormalisedCurrent.measure R h2 1%N 0%N
  Full hFull boundary hInterval.1.2).
Local Notation Op := (@euclidean_operator_norm R 1%N 1%N).
Local Notation rho := (fun x:UT=>Num.max
  (Op (@current_map_differential R 1%N 1%N Full Id (set_val x)))
  (Op (@current_map_differential R 1%N 1%N Full Id (set_val x)))).

(** Source for [affine_identity_interval_mass_one]: the actual
    identity-map regression uses a nonzero normal one-current.
    Its original interval mass is one by 4.1.8, p. 362, and
    4.1.12, pp. 368–369, supporting the positive-degree estimate
    of Federer 4.1.13, pp. 369–370. *)
Example affine_identity_interval_mass_one:
  @CurrentMass.value R h2 1%N 1%N Full hFull interval= 1%:E.
Proof.
rewrite (@oriented_segment_current_mass R h2 1%N Full hFull
  (@euclidean_one_embed R 0) one segmentDomain).
have hZero:(@euclidean_one_embed R 0)=(0:X).
  apply/ffunP=>i;by rewrite /euclidean_one_embed ffunE.
by rewrite hZero subr0 euclidean_one_norm_coordinate
  /euclidean_one_embed ffunE normr1.
Qed.

(** Source for [affine_identity_interval_flat_value_zero]: apply
    the final positive-degree assertion of Federer 4.1.13,
    pp. 369–370, to the actual normal interval and two identity
    maps. Both original variation integrals vanish, including the
    boundary integral, with the exact original compact index. *)
Example affine_identity_interval_flat_value_zero:
  @current_flat_norm R h2 1%N 1%N Full hFull K (P-P)=0%E.
Proof.
have h:=@federer_4_1_13_positive R h2 1%N 1%N 0%N
  Full Full hFull hFull Id Id hImage hImage hId hId
  interval hInterval hHull.
have hWeight k:(fun x:UT=>NX (set_val x-set_val x)*(rho x)^+k)=
    (fun _:UT=>(0:R)).
  apply:funext=>x;by rewrite subrr
    (real_seminorm_zero hNX.1) mul0r.
change (is_true (@current_flat_norm R h2 1%N 1%N Full hFull K (P-P)<=
  measure_lower_integral mu (real_total_integrand
    (fun x:UT=>(NX (set_val x-set_val x)*(rho x)^+1%N)%R))+
  measure_lower_integral muB (real_total_integrand
    (fun x:UT=>(NX (set_val x-set_val x)*(rho x)^+0%N)%R)))%E) in h.
rewrite (hWeight 1%N) (hWeight 0%N)
  (affine_endpoint_zero_lower_value
    (distribution_representation_measure
      (normalised_distribution_representation_laws
        (@NormalisedCurrent.laws R h2 1%N 1%N Full hFull
          interval hInterval.1.1))))
  (affine_endpoint_zero_lower_value
    (distribution_representation_measure
      (normalised_distribution_representation_laws
        (@NormalisedCurrent.laws R h2 1%N 0%N Full hFull
          boundary hInterval.1.2)))) adde0 in h.
have hNonnegative:=@current_flat_dual_nonnegative R h2 1%N 1%N
  Full hFull K (@current_value R h2 1%N Full hFull 1%N (P-P)).
apply/eqP;by rewrite eq_le h hNonnegative.
Qed.
End AffineCurrentEndpointExamples.

Section AffineTranslatedPointEndpoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Y := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R 0%N)).
Local Notation hNY := (inner_norm_real_norm
  (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>True).
Local Notation V := (fun _:Y=>True).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hV := (fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation one := (@euclidean_one_embed R 1).
Local Notation f := (fun _:X=>(0:Y)).
Local Notation g := (fun _:X=>one).
Local Notation hf := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U (0:Y) k hU).
Local Notation hg := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U one k hU).
Local Notation hFImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation hGImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation T := (@dirac_current R h2 0%N U hU (0:X)).
Local Notation hNormal := (@dirac_current_normal R h2 0%N U hU (0:X) Logic.I).
Local Notation hC := (fun (y:Y)
  (_:@current_affine_segment_hull R h2 0%N 1%N 0%N U hU f g T y)=>Logic.I).
Local Notation C := (@current_affine_image_compact R h2 0%N 1%N 0%N
  U V hU f g hf hg T hNormal hC).

(** Source for [affine_zero_dimensional_point_nonzero]: the
    degree-zero regression for Federer 4.1.13, pp. 369–370,
    starts with the actual nonzero unit point current in R^0.
    An original compact test of value one witnesses nonvanishing. *)
Example affine_zero_dimensional_point_nonzero:T<>0.
Proof.
move=>hZero.
have[psi hOne]:=@dirac_current_unit_test R h2 0%N U hU (0:X) Logic.I.
rewrite hZero (linear0 (@current_value R h2 0%N U hU 0%N))
  hom_zeroE in hOne.
have hBad:(1:R)=0:=esym hOne.
by have:=@oner_neq0 R;rewrite hBad eqxx.
Qed.

(** Source for [affine_translated_point_flat_bound]: the final
    zero-degree theorem of Federer 4.1.13, pp. 369–370, gives
    F_[0,1](delta_1-delta_0)<=1 for the actual point images of
    the nonzero R^0 current. The original variation integral is
    evaluated by the proved point-mass formula, not assumed. *)
Example affine_translated_point_flat_bound:
  (@current_flat_norm R h2 1%N 0%N V hV C
    (@dirac_current R h2 1%N V hV one-
      @dirac_current R h2 1%N V hV (0:Y))<=1%:E)%E.
Proof.
have h:=@federer_4_1_13_zero R h2 0%N 1%N U V hU hV f g
  hFImage hGImage hf hg T hNormal hC.
rewrite (@current_compact_map_dirac_image R h2 0%N 1%N U V hU hV
  f hFImage hf (0:X) Logic.I hNormal.2)
  (@current_compact_map_dirac_image R h2 0%N 1%N U V hU hV
  g hGImage hg (0:X) Logic.I hNormal.2) in h.
rewrite (@current_dirac_variation R h2 0%N U hU (0:X)
  Logic.I hNormal.1.1) in h.
pose c:=@current_dirac_domain_point R 0%N U (0:X) Logic.I.
pose weight:=fun x:current_domain R 0%N U=>NY (g (set_val x)-f (set_val x)).
have hIntegral:=@point_mass_real_integral R (current_domain R 0%N U) c weight.
have hValue:=measure_lower_integral_unique
  (measure_lower_integral_specification _ (real_total_integrand weight))
  hIntegral.2.2.
change (measure_lower_integral (PointMassMeasure.point_mass R c) (real_total_integrand weight)=
  (NY (one-0))%:E) in hValue.
have hLength:NY (one-0)= 1.
  by rewrite subr0 euclidean_one_norm_coordinate
    /euclidean_one_embed ffunE normr1.
rewrite hValue hLength in h.
exact:h.
Qed.
End AffineTranslatedPointEndpoint.

Section AffineEmptySourceEndpoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Y := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R 0%N)).
Local Notation hNY := (inner_norm_real_norm
  (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>False).
Local Notation V := (fun _:Y=>False).
Local Notation hU := (fun (x:X) (hx:False)=>
  False_rect (norm_domain_interior NX U x) hx).
Local Notation hV := (fun (y:Y) (hy:False)=>
  False_rect (norm_domain_interior NY V y) hy).
Local Notation f := (fun _:X=>(0:Y)).
Local Notation g := (fun _:X=>@euclidean_one_embed R 1).
Local Notation hf := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U (0:Y) k hU).
Local Notation hg := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U (@euclidean_one_embed R 1) k hU).
Local Notation hFImage := (fun (x:X) (hx:False)=>hx).
Local Notation hGImage := (fun (x:X) (hx:False)=>hx).
Local Notation T := (0:@current_space R h2 0%N U hU 0%N).
Local Notation hNormal := (@normal_current_zero R h2 0%N U hU 0%N).

(** Source for [affine_empty_segment_hull_in_empty_target]: for
    the actual zero current on the empty source, the original
    segment hull is empty, checking the literal source and target
    hypotheses of Federer 4.1.13, pp. 369–370. The total map
    representatives may differ outside the original empty domain. *)
Lemma affine_empty_segment_hull_in_empty_target:
  @current_affine_segment_hull R h2 0%N 1%N 0%N U hU f g T `<=` V.
Proof.
move=>y [t [x [ht [hx hValue]]]];exact:hx.1.
Qed.
Local Notation hC := affine_empty_segment_hull_in_empty_target.
Local Notation C := (@current_affine_image_compact R h2 0%N 1%N 0%N
  U V hU f g hf hg T hNormal hC).
Local Notation F := (@current_compact_map_pushforward R h2 0%N 1%N
  U V hU hV f hFImage hf 0%N T hNormal.2).
Local Notation G := (@current_compact_map_pushforward R h2 0%N 1%N
  U V hU hV g hGImage hg 0%N T hNormal.2).
Local Notation mu := (@NormalisedCurrent.measure R h2 0%N 0%N
  U hU T hNormal.1.1).

(** Source for [affine_empty_source_target_flat_value_zero]:
    apply the final zero-degree theorem of Federer 4.1.13,
    pp. 369–370, with empty original source and target. The
    variation integral vanishes on its actual empty domain and
    the compact index remains the original empty segment hull. *)
Example affine_empty_source_target_flat_value_zero:
  @current_flat_norm R h2 1%N 0%N V hV C (G-F)=0%E.
Proof.
have h:=@federer_4_1_13_zero R h2 0%N 1%N U V hU hV f g
  hFImage hGImage hf hg T hNormal hC.
have hWeight:(fun x:current_domain R 0%N U=>
    NY (g (set_val x)-f (set_val x)))=
    (fun _:current_domain R 0%N U=>(0:R)).
  apply:funext=>x;case:(set_valP x).
rewrite hWeight
  (affine_endpoint_zero_lower_value
    (distribution_representation_measure
      (normalised_distribution_representation_laws
        (@NormalisedCurrent.laws R h2 0%N 0%N U hU T hNormal.1.1)))) in h.
have hNonnegative:=@current_flat_dual_nonnegative R h2 1%N 0%N
  V hV C (@current_value R h2 1%N V hV 0%N (G-F)).
apply/eqP;by rewrite eq_le h hNonnegative.
Qed.
End AffineEmptySourceEndpoint.

Section AffineSupportOnlyTargetEndpoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Y := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R 0%N)).
Local Notation hNY := (inner_norm_real_norm
  (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>True).
Local Notation V := (fun y:Y=>0<NY y).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation one := (@euclidean_one_embed R 1).
Local Notation f := (fun _:X=>-one).
Local Notation g := (fun _:X=>one).
Local Notation T := (0:@current_space R h2 0%N U hU 0%N).
Local Notation hNormal := (@normal_current_zero R h2 0%N U hU 0%N).
Local Notation hf := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U (-one) k hU).
Local Notation hg := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U one k hU).

(** Source for [affine_punctured_target_open]: the actual punctured
    R^1 is an original open target, checking the absence of a
    convex-target hypothesis in Federer 4.1.13, pp. 369–370.
    The triangle inequality gives the required positive ball margin. *)
Lemma affine_punctured_target_open y:
  V y->norm_domain_interior NY V y.
Proof.
move=>hy;change (is_true (0<NY y)) in hy.
exists (NY y/2);split;first by rewrite divr_gt0 // ltr0n.
move=>z hz.
have hTriangle:=real_seminorm_triangle hNY.1 (y+z) (-z).
rewrite addrK (real_seminorm_negate hNY.1) in hTriangle.
lra.
Qed.
Local Notation hV := affine_punctured_target_open.

(** Source for [affine_punctured_endpoint_images]: both original
    endpoint maps have values in the nonconvex punctured target,
    checking Federer 4.1.13, pp. 369–370. Their affine path on
    the whole nonempty source will fail that target condition. *)
Lemma affine_punctured_endpoint_images:
  (forall x,U x->V (f x)) /\ (forall x,U x->V (g x)).
Proof.
have hOne:NY one= 1.
  by rewrite euclidean_one_norm_coordinate
    /euclidean_one_embed ffunE normr1.
split=>x _;last by rewrite /V hOne.
by rewrite /V (real_seminorm_negate hNY.1) hOne.
Qed.
Local Notation hFImage := affine_punctured_endpoint_images.1.
Local Notation hGImage := affine_punctured_endpoint_images.2.

(** Source for [affine_zero_support_hull_in_punctured_target]:
    the exact C is empty for the actual zero current, although its
    original source is nonempty. This checks the support-only image
    hypothesis of Federer 4.1.13, pp. 369–370. *)
Lemma affine_zero_support_hull_in_punctured_target:
  @current_affine_segment_hull R h2 0%N 1%N 0%N U hU f g T `<=` V.
Proof.
have hEmpty: @current_support R h2 0%N U hU 0%N T `<=` set0.
  exact:(@current_empty_support_iff_zero R h2 0%N 0%N U hU T).2 (erefl T).
move=>y [t [x [ht [hx hValue]]]].
exact:(False_ind _ (hEmpty x hx)).
Qed.
Local Notation hC := affine_zero_support_hull_in_punctured_target.
Local Notation C := (@current_affine_image_compact R h2 0%N 1%N 0%N
  U V hU f g hf hg T hNormal hC).
Local Notation F := (@current_compact_map_pushforward R h2 0%N 1%N
  U V hU hV f hFImage hf 0%N T hNormal.2).
Local Notation G := (@current_compact_map_pushforward R h2 0%N 1%N
  U V hU hV g hGImage hg 0%N T hNormal.2).
Local Notation mu := (@NormalisedCurrent.measure R h2 0%N 0%N
  U hU T hNormal.1.1).

(** Source for [affine_support_only_target_regression]: the final
    original theorem of Federer 4.1.13, pp. 369–370, applies
    although the affine path leaves the target at time one half
    on the original nonempty source. This guards against replacing
    C subset V by a stronger whole-source image hypothesis. *)
Example affine_support_only_target_regression:
  ~(forall (t:R) (x:X),0<=t<=1->U x->
    V ((1-t)*:f x+t*:g x)) /\
  (@current_flat_norm R h2 1%N 0%N V hV C (G-F)<=
    measure_lower_integral mu (real_total_integrand
      (fun x:current_domain R 0%N U=>
        NY (g (set_val x)-f (set_val x)))))%E.
Proof.
split.
- move=>hGlobal.
  have hHalf:0<=(1/2:R)<=1 by apply/andP;split;lra.
  have hBad:=hGlobal (1/2) (0:X) hHalf Logic.I.
  have hCoefficient:(1-1/2:R)= 1/2 by lra.
  have hZero:((1-1/2:R)*:(-one)+(1/2:R)*:one)=(0:Y).
    by rewrite hCoefficient scalerN addNr.
  move:hBad;by rewrite hZero /V (real_seminorm_zero hNY.1) ltxx.
- exact:(@federer_4_1_13_zero R h2 0%N 1%N U V hU hV f g
    hFImage hGImage hf hg T hNormal hC).
Qed.
End AffineSupportOnlyTargetEndpoint.
