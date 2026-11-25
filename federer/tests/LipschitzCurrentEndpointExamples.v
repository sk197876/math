(** Actual-space endpoint regressions for Federer (1969),
    4.1.14, pp. 370–372. Exercise the final sealed
    compact Lipschitz image on empty opens, an empty compact
    index, a zero current on a nonempty index, an actual
    nonzero point in R^0 under a constant map of least
    Lipschitz constant zero, and a nonzero normal interval
    under identity and constant maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanOneNormDifferential
  LipschitzUP LipschitzBasic LipschitzConstant
  AlternatingForms CurrentSpaces CurrentDirac DiracCurrentBounds
  CurrentSupportGeometry SmoothCompactSet NormalCurrentsUP NormalCurrentLinear
  FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage
  CurrentCompactPushforwardAlgebra CurrentCompactElementaryPushforwards
  CurrentElementaryPushforwards CurrentOpenIdentitySmooth
  CurrentSegmentMapUP ScalarSegmentCoordinateValues CurrentSegmentCompactSet
  OrientedSegmentCurrentSealed OrientedSegmentNormal OrientedSegmentCurrentSupport
  OrientedSegmentMass CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentCompactLipschitzPushforwardSealed CurrentCompactLipschitzPushforwardSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_endpoint_constant_local]: constant
    maps satisfy the original local hypothesis even on
    empty domains, by 2.2.7, p. 64; supporting
    the actual endpoint regressions of 4.1.14, p. 370. *)
Local Lemma lipschitz_endpoint_constant_local (R:realType)
    (X Y:metricType R) (U:set X) (a:Y):
  is_locally_metric_lipschitz U (fun _:X=>a).
Proof.
apply:metric_lipschitz_is_local.
exact:(metric_lipschitz_of_bound
  (least_metric_lipschitz_bound (@metric_lipschitz_constant_map R X Y U a))).
Qed.

(** Source for [lipschitz_endpoint_zero_flat]: the original
    zero current belongs to every fixed-index flat space,
    by 4.1.12, p. 368; supporting 4.1.14,
    p. 370, with empty and nonempty compact indices. *)
Local Lemma lipschitz_endpoint_zero_flat (R:realType) (h2:(1+1:R)!=0)
    n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
  @is_flat_current_supported_in R h2 n m U hU K 0.
Proof.
apply:supported_normal_current_is_flat;split.
- exact:normal_current_zero.
- exact:current_support_zero_subset.
Qed.

(** Source for [lipschitz_endpoint_dirac_nonzero]: an original
    unit point test detects the nonzero point current,
    by 4.1.7, p. 359; supporting the degree-zero
    constant-image endpoint of 4.1.14, pp. 370–371. *)
Local Lemma lipschitz_endpoint_dirac_nonzero (R:realType) (h2:(1+1:R)!=0)
    n (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x) a:
  U a->@dirac_current R h2 n U hU a<>0.
Proof.
move=>ha hZero.
have[psi hOne]:=@dirac_current_unit_test R h2 n U hU a ha.
rewrite hZero (linear0 (@current_value R h2 n U hU 0%N)) hom_zeroE in hOne.
have hBad:(1:R)=0:=esym hOne.
by have:=@oner_neq0 R;rewrite hBad eqxx.
Qed.

Section LipschitzEmptySourceTargetEndpoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Y := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>False).
Local Notation V := (fun _:Y=>False).
Local Notation hU := (fun (x:X) (hx:False)=>False_ind (norm_domain_interior NX U x) hx).
Local Notation hV := (fun (y:Y) (hy:False)=>False_ind (norm_domain_interior NY V y) hy).
Local Notation f := (fun _:X=>(0:Y)).
Local Notation hImage := (fun (x:X) (hx:False)=>hx).
Local Notation hLocal := (@lipschitz_endpoint_constant_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U (0:Y)).
Local Notation hSmooth := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U (0:Y) k hU).
Local Notation K := (@smooth_compact_empty R X NX hNX U).
Local Notation T := (0:@current_space R h2 0%N U hU 0%N).
Local Notation hFlat := (@lipschitz_endpoint_zero_flat R h2 0%N 0%N U hU K).

(** Source for [lipschitz_empty_source_target_zero]: the
    final original compact operator exists and sends zero
    to zero when U, V and K are empty, checking
    Federer 4.1.14, p. 370, without a target point. *)
Example lipschitz_empty_source_target_zero:
  @CurrentCompactLipschitzPushforward.value R h2 0%N 1%N 0%N
    U V hU hV f hImage hLocal K T hFlat=0.
Proof.
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 0%N 1%N 0%N
  U V hU hV f hImage hLocal K T hFlat hSmooth).
exact:(@current_compact_map_pushforward_zero R h2 0%N 1%N U V hU hV
  f hImage hSmooth 0%N T
  (@flat_supported_current_compact R h2 0%N 0%N U hU K T hFlat) (erefl T)).
Qed.
End LipschitzEmptySourceTargetEndpoint.

Section LipschitzZeroEndpoints.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation U := (fun _:X=>True).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation f := (fun _:X=>(0:X)).
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation hLocal := (@lipschitz_endpoint_constant_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNX) U (0:X)).
Local Notation hSmooth := (fun k=>@norm_class_constant R X X NX NX hNX hNX
  U (0:X) k hU).
Local Notation Empty := (@smooth_compact_empty R X NX hNX U).
Local Notation Point := (@smooth_compact_singleton R X NX hNX U (0:X) Logic.I).
Local Notation T := (0:@current_space R h2 0%N U hU 0%N).

(** Source for [lipschitz_empty_compact_nonempty_opens_zero]:
    an empty K with nonempty original opens retains the
    final compact Lipschitz value, checking the independent
    empty-index case of Federer 4.1.14, p. 370. *)
Example lipschitz_empty_compact_nonempty_opens_zero:
  @CurrentCompactLipschitzPushforward.value R h2 0%N 0%N 0%N
    U U hU hU f hImage hLocal Empty T
    (@lipschitz_endpoint_zero_flat R h2 0%N 0%N U hU Empty)=0.
Proof.
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 0%N 0%N 0%N
  U U hU hU f hImage hLocal Empty T
  (@lipschitz_endpoint_zero_flat R h2 0%N 0%N U hU Empty) hSmooth).
exact:current_compact_map_pushforward_zero (erefl T).
Qed.

(** Source for [lipschitz_zero_current_nonempty_index]: the
    zero current on a nonempty original compact index
    has zero image under the final actual operator,
    checking Federer 4.1.14, pp. 370–371. *)
Example lipschitz_zero_current_nonempty_index:
  @CurrentCompactLipschitzPushforward.value R h2 0%N 0%N 0%N
    U U hU hU f hImage hLocal Point T
    (@lipschitz_endpoint_zero_flat R h2 0%N 0%N U hU Point)=0.
Proof.
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 0%N 0%N 0%N
  U U hU hU f hImage hLocal Point T
  (@lipschitz_endpoint_zero_flat R h2 0%N 0%N U hU Point) hSmooth).
exact:current_compact_map_pushforward_zero (erefl T).
Qed.
End LipschitzZeroEndpoints.

Section LipschitzZeroDimensionalPointEndpoint.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Y := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>True).
Local Notation V := (fun _:Y=>True).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hV := (fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation one := (@euclidean_one_embed R 1).
Local Notation f := (fun _:X=>one).
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation hLocal := (@lipschitz_endpoint_constant_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U one).
Local Notation hSmooth := (fun k=>@norm_class_constant R X Y NX NY hNX hNY
  U one k hU).
Local Notation K := (@smooth_compact_singleton R X NX hNX U (0:X) Logic.I).
Local Notation P := (@dirac_current R h2 0%N U hU (0:X)).
Local Notation Q := (@dirac_current R h2 1%N V hV one).
Local Notation hLipK := (@metric_lipschitz_of_bound R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (smooth_compact_carrier K) f 0 (least_metric_lipschitz_bound
    (@metric_lipschitz_constant_map R (real_norm_metric_space hNX)
      (real_norm_metric_space hNY) (smooth_compact_carrier K) one))).
Local Notation L := (metric_lipschitz_constant hLipK).

(** Source for [lipschitz_point_flat_member]: the nonzero
    original R^0 point is flat with its singleton
    compact index, by 4.1.12, p. 368, supporting
    the degree-zero endpoint of 4.1.14, p. 371. *)
Local Lemma lipschitz_point_flat_member:
  @is_flat_current_supported_in R h2 0%N 0%N U hU K P.
Proof.
apply:supported_normal_current_is_flat;split.
- exact:(@dirac_current_normal R h2 0%N U hU (0:X) Logic.I).
- exact:(@dirac_current_support_subset R h2 0%N U hU (0:X) Logic.I).
Qed.
Local Notation image := (@CurrentCompactLipschitzPushforward.value R h2
  0%N 1%N 0%N U V hU hV f hImage hLocal K P lipschitz_point_flat_member).

(** Source for [lipschitz_zero_dimensional_point_constant]: a
    constant map of least Lipschitz constant zero preserves
    a nonzero degree-zero point image. Its zero exponent
    is one, as required by the exact degree-zero bound
    of Federer 4.1.14, pp. 370–371. *)
Example lipschitz_zero_dimensional_point_constant:
  P<>0 /\L=0 /\L^+0%N = 1 /\image=Q /\image<>0.
Proof.
have hPoint:P<>0:=@lipschitz_endpoint_dirac_nonzero R h2 0%N U hU (0:X) Logic.I.
have hZero:L=0.
  exact:(@least_metric_lipschitz_unique R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (smooth_compact_carrier K) f L 0
    (metric_lipschitz_constant_specification hLipK)
    (@metric_lipschitz_constant_map R (real_norm_metric_space hNX)
      (real_norm_metric_space hNY) (smooth_compact_carrier K) one)).
have hImagePoint:image=Q.
  rewrite (@current_compact_lipschitz_pushforward_smooth R h2 0%N 1%N 0%N
    U V hU hV f hImage hLocal K P lipschitz_point_flat_member hSmooth).
  exact:(@current_compact_map_dirac_image R h2 0%N 1%N U V hU hV
    f hImage hSmooth (0:X) Logic.I
    (@flat_supported_current_compact R h2 0%N 0%N U hU K P lipschitz_point_flat_member)).
split;first exact:hPoint.
split;first exact:hZero.
split;first by rewrite expr0.
split;first exact:hImagePoint.
rewrite hImagePoint;exact:(@lipschitz_endpoint_dirac_nonzero R h2 1%N V hV one Logic.I).
Qed.
End LipschitzZeroDimensionalPointEndpoint.

Section LipschitzIntervalEndpoints.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>True).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation one := (@euclidean_one_embed R 1).
Local Notation hSegment := (@scalar_segment_full_domain R 0 1).
Local Notation T := (@OrientedSegmentCurrent.value R h2 1%N U hU
  (@euclidean_one_embed R 0) one hSegment).
Local Notation K := (@current_segment_compact_set R 1%N U
  (@euclidean_one_embed R 0) one hSegment).
Local Notation Id := (fun x:X=>x).
Local Notation Cst := (fun _:X=>(0:X)).
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation hId := (@current_open_identity_smooth R 1%N U hU).
Local Notation hConstant := (fun k=>@norm_class_constant R X X NX NX hNX hNX
  U (0:X) k hU).
Local Notation hConstantLocal := (@lipschitz_endpoint_constant_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNX) U (0:X)).

(** Source for [lipschitz_interval_flat_member]: the actual
    normal unit interval is flat in its original segment
    compact index, by 4.1.8, p. 362, and
    4.1.12, p. 368, supporting 4.1.14, p. 371. *)
Local Lemma lipschitz_interval_flat_member:
  @is_flat_current_supported_in R h2 1%N 1%N U hU K T.
Proof.
apply:supported_normal_current_is_flat;split.
- exact:(@oriented_segment_current_normal R h2 1%N U hU
    (@euclidean_one_embed R 0) one hSegment).
- exact:(@oriented_segment_current_support R h2 1%N U hU
    (@euclidean_one_embed R 0) one hSegment).
Qed.

(** Source for [lipschitz_interval_nonzero]: the original
    interval has mass one and is nonzero, by
    4.1.8, p. 362, supporting the actual positive-degree
    endpoint of Federer 4.1.14, pp. 370–371. *)
Local Lemma lipschitz_interval_nonzero:T<>0.
Proof.
have hMass:@CurrentMass.value R h2 1%N 1%N U hU T= 1%:E.
  rewrite (@oriented_segment_current_mass R h2 1%N U hU
    (@euclidean_one_embed R 0) one hSegment).
  have hZero:(@euclidean_one_embed R 0)=(0:X).
    apply/ffunP=>i;by rewrite /euclidean_one_embed ffunE.
  by rewrite hZero subr0 euclidean_one_norm_coordinate
    /euclidean_one_embed ffunE normr1.
move=>hZero;rewrite hZero current_mass_zero in hMass.
have hBad:(0:R)= 1:=EFin_inj hMass.
by have:=@oner_neq0 R;rewrite -hBad eqxx.
Qed.

(** Source for [lipschitz_identity_local]: the identity is
    locally Lipschitz on the original open source, by
    2.2.7, p. 64, supporting the final identity
    image regression for 4.1.14, p. 371. *)
Local Lemma lipschitz_identity_local:
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNX) U Id.
Proof.
apply:metric_lipschitz_is_local.
exists 1;split;first exact:ltr01.
split;first exact:ler01.
by move=>x y _ _;rewrite mul1r.
Qed.

(** Source for [lipschitz_positive_constant_interval_zero]:
    the final sealed image kills the nonzero interval
    in positive degree under a constant map, retaining
    the sharp zero-constant endpoint of 4.1.14, p. 371. *)
Example lipschitz_positive_constant_interval_zero:
  T<>0 /\@CurrentCompactLipschitzPushforward.value R h2 1%N 1%N 1%N
    U U hU hU Cst hImage hConstantLocal K T lipschitz_interval_flat_member=0.
Proof.
split;first exact:lipschitz_interval_nonzero.
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 1%N 1%N 1%N
  U U hU hU Cst hImage hConstantLocal K T lipschitz_interval_flat_member hConstant).
exact:(@current_compact_constant_positive_pushforward R h2 1%N U hU 0%N
  U hU (0:X) T
  (@flat_supported_current_compact R h2 1%N 1%N U hU K T lipschitz_interval_flat_member)
  hImage hConstant _).
Qed.

(** Source for [lipschitz_identity_nonzero_interval]: the
    final original compact Lipschitz operator fixes the
    actual nonzero interval under identity, checking the
    formal properties in Federer 4.1.14, p. 371. *)
Example lipschitz_identity_nonzero_interval:
  @CurrentCompactLipschitzPushforward.value R h2 1%N 1%N 1%N
    U U hU hU Id hImage lipschitz_identity_local K T lipschitz_interval_flat_member=T /\T<>0.
Proof.
split;last exact:lipschitz_interval_nonzero.
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 1%N 1%N 1%N
  U U hU hU Id hImage lipschitz_identity_local K T lipschitz_interval_flat_member hId).
exact:(@current_compact_identity_pushforward R h2 1%N U hU 1%N T
  (@flat_supported_current_compact R h2 1%N 1%N U hU K T lipschitz_interval_flat_member)
  hImage hId _).
Qed.
End LipschitzIntervalEndpoints.
