(** Federer (1969), 4.1.14, p. 371: changing
    the open time interval and the source neighbourhood
    leaves the original interval-current product unchanged
    under identity inclusion. Reuse Cartesian naturality
    and the original all-test oriented segment action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentCartesianMapClass
  CurrentCartesianMapPullback
  CurrentSpaces CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeSegment OrientedSegmentNormal OrientedSegmentOpenRestriction
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentCartesianProductPushforward CurrentCompactMapProper CurrentOpenIdentitySmooth
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentPushforwardSealed CurrentPushforwardDataIndependence
  CurrentNeighbourhoodInclusion CurrentFlatNeighbourhoodRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTimeProductNeighbourhood.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variables A B : set R.
Variables U W : set (R_n R n).
Hypothesis hA : @is_homotopy_parameter_interval R A.
Hypothesis hB : @is_homotopy_parameter_interval R B.
Local Notation X := (R_n R n).
Local Notation Line := (R_n R 1%N).
Local Notation Product := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NL := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation NP := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNL := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNP := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hW : forall x, W x -> norm_domain_interior NX W x.
Hypothesis hBA : forall t, B t -> A t.
Hypothesis hWU : forall x, W x -> U x.
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation BT := (@current_homotopy_time_domain R B).
Local Notation hAT := (@current_homotopy_time_domain_open R A hA).
Local Notation hBT := (@current_homotopy_time_domain_open R B hB).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation BW := (@current_homotopy_product_domain R n B W).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation hBW := (@current_cartesian_domain_open R 1%N n BT W hBT hW).
Let hBTAT : forall t, BT t -> AT t := fun t ht => @hBA _ ht.
Let hBWAU : forall z, BW z -> AU z :=
  fun z hz => conj (@hBTAT _ hz.1) (@hWU _ hz.2).
Variable T : @current_space R h2 n U hU m.
Hypothesis hCompact : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Hypothesis hSupportW : @current_support R h2 n U hU m T `<=` W.
Local Notation S := (@current_open_restriction R h2 n m W U hW hU hWU T).
Local Notation TimeA := (@current_homotopy_time_segment R A hA h2).
Local Notation TimeB := (@current_homotopy_time_segment R B hB h2).
Local Notation Large := (@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT U hAT hU TimeA T).
Local Notation Small := (@CartesianCurrentProduct.value R h2 1%N n 1%N m
  BT W hBT hW TimeB S).

(** Source for [current_time_neighbourhood_restricted_compact]:
    restricting to an open neighbourhood of spt T preserves
    its compact support, supporting the source change in
    Federer 4.1.14, p. 371. T is arbitrary. *)
Lemma current_time_neighbourhood_restricted_compact :
  @compact (real_norm_metric_space hNX) (@current_support R h2 n W hW m S).
Proof.
have hSupport : @current_support R h2 n W hW m S=
    @current_support R h2 n U hU m T.
  rewrite current_open_restriction_support.
  apply: funext=> x; apply: propext; split.
  - by move=> [_ hx].
  - move=> hx; exact: conj (@hSupportW x hx) hx.
by rewrite hSupport.
Qed.

(** Source for [current_time_product_neighbourhood_compact]:
    the actual [0,1] times the restricted compact current
    has compact support, supporting Federer 4.1.14,
    p. 371, by the Cartesian compactness of 4.1.8. *)
Lemma current_time_product_neighbourhood_compact :
  @compact (real_norm_metric_space hNP)
    (@current_support R h2 (1+n)%N BW hBW (1+m)%N Small).
Proof.
have hTime := (@oriented_segment_current_normal R h2 1%N BT hBT
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
  (@current_homotopy_time_segment_domain R B hB)).2.
exact: (@current_cartesian_compact_currents R h2 1%N n 1%N m BT W hBT hW
  TimeB S hTime current_time_neighbourhood_restricted_compact).
Qed.

(** Source for [current_time_product_neighbourhood_inclusion]:
    inclusion from B times W into A times U sends
    intervalB times R_WT to intervalA times T, supporting
    the original homotopy neighbourhood independence in Federer
    4.1.14, p. 371. Every compactness witness is allowed.
    No flatness, normality or finite-mass premise is imposed on T. *)
Theorem current_time_product_neighbourhood_inclusion
    (hSmall : @compact (real_norm_metric_space hNP)
      (@current_support R h2 (1+n)%N BW hBW (1+m)%N Small)) :
  @current_compact_map_pushforward R h2 (1+n)%N (1+n)%N BW AU hBW hAU
    (fun z:Product => z) hBWAU (@current_open_identity_smooth R (1+n)%N BW hBW)
    (1+m)%N Small hSmall=Large.
Proof.
pose hTime := (@oriented_segment_current_normal R h2 1%N BT hBT
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
  (@current_homotopy_time_segment_domain R B hB)).2.
pose hS := current_time_neighbourhood_restricted_compact.
pose hCanonical := @current_cartesian_compact_currents R h2 1%N n 1%N m
  BT W hBT hW TimeB S hTime hS.
pose hFullTime := fun t (_:True) => @norm_full_domain_interior R Line NL t.
pose hFullSource := fun x (_:True) => @norm_full_domain_interior R X NX x.
pose hf := @current_open_identity_smooth R 1%N (fun _:Line => True) hFullTime.
pose hg := @current_open_identity_smooth R n (fun _:X => True) hFullSource.
pose hFirstClass := @current_cartesian_factor_open_class R 1%N 1%N BT hBT
  (fun t:Line => t) hf.
pose hSecondClass := @current_cartesian_factor_open_class R n n W hW
  (fun x:X => x) hg.
pose F := @euclidean_cartesian_map R 1%N n 1%N n
  (fun t:Line => t) (fun x:X => x).
pose hFImage := fun z (hz:BW z) =>
  @current_cartesian_map_domain_image R 1%N n 1%N n BT W AT U
    (fun t:Line => t) (fun x:X => x) hBTAT hWU z hz.
pose hFClass := @current_cartesian_map_on_open_product_smooth R 1%N n 1%N n
  (fun t:Line => t) (fun x:X => x) hf hg BT W hBT hW.
have hOld := @current_cartesian_product_pushforward R h2 1%N n 1%N n
  BT W AT U hBT hW hAT hU (fun t:Line => t) (fun x:X => x)
  hf hg hBTAT hWU 1%N m TimeB S hTime hS.
have hSame := @current_compact_map_images_agree R h2 (1+n)%N (1+n)%N
  BW AU hBW hAU F hFImage hFClass (1+m)%N Small hCanonical
  (fun z:Product => z) hBWAU (@current_open_identity_smooth R (1+n)%N BW hBW) hSmall.
have hFIdentity : forall z, BW z -> F z=z.
  move=> z _; rewrite /F /euclidean_cartesian_map
    -(surjective_pairing (@euclidean_block_split R 1%N n z)).
  exact: euclidean_block_splitK.
have hFirst :
    @current_compact_map_pushforward R h2 1%N 1%N BT AT hBT hAT
      (fun t:Line => t) hBTAT hFirstClass 1%N TimeB hTime=TimeA.
  have hAlign : @current_compact_map_pushforward R h2 1%N 1%N BT AT hBT hAT
      (fun t:Line => t) hBTAT hFirstClass 1%N TimeB hTime=
    @current_compact_map_pushforward R h2 1%N 1%N BT AT hBT hAT
      (fun t:Line => t) hBTAT (@current_open_identity_smooth R 1%N BT hBT)
      1%N TimeB hTime.
    exact: current_pushforward_data_independent.
  apply: (eq_trans hAlign).
  exact: (@oriented_segment_open_inclusion R h2 1%N AT BT hAT hBT hBTAT
    (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
    (@current_homotopy_time_segment_domain R A hA)
    (@current_homotopy_time_segment_domain R B hB) hTime).
have hSecond :
    @current_compact_map_pushforward R h2 n n W U hW hU (fun x:X => x)
      hWU hSecondClass m S hS=T.
  exact: (@current_neighbourhood_inclusion_recovery R h2 n m W U hW hU hWU
    hSecondClass T hSupportW
    (@current_compact_map_proper R h2 n n m W U hW S (fun x:X => x) hWU
      (norm_class_continuous (hSecondClass 0%N)) hS)).
change (@current_compact_map_pushforward R h2 (1+n)%N (1+n)%N BW AU hBW hAU
  F hFImage hFClass (1+m)%N Small hCanonical=
  @CartesianCurrentProduct.value R h2 1%N n 1%N m AT U hAT hU
    (@current_compact_map_pushforward R h2 1%N 1%N BT AT hBT hAT
      (fun t:Line => t) hBTAT hFirstClass 1%N TimeB hTime)
    (@current_compact_map_pushforward R h2 n n W U hW hU
      (fun x:X => x) hWU hSecondClass m S hS)) in hOld.
rewrite hFirst hSecond in hOld.
exact: eq_trans (esym (hSame hFIdentity)) hOld.
Qed.

(** Source for [current_time_product_neighbourhood_restriction]:
    the same interval product restricted to B times W
    is intervalB times R_WT, supporting Federer 4.1.14,
    p. 371. Use the preceding actual inclusion identity
    and the old inclusion-restriction inverse. *)
Theorem current_time_product_neighbourhood_restriction :
  @current_open_restriction R h2 (1+n)%N (1+m)%N BW AU hBW hAU hBWAU Large=Small.
Proof.
have hCompactSmall := current_time_product_neighbourhood_compact.
have hInclusion := current_time_product_neighbourhood_inclusion hCompactSmall.
exact: esym (@current_compact_representative_is_open_restriction R h2 (1+n)%N
  (1+m)%N AU BW hAU hBW hBWAU Large Small hCompactSmall hInclusion).
Qed.
End CurrentTimeProductNeighbourhood.
