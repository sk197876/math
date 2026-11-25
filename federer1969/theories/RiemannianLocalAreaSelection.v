(** Federer (1969), 3.2.46, p. 282: the
    Borel selection of 3.2.4, p. 244, in actual
    Riemannian coordinates. Local Euclidean extensions give
    a univalent positive-Jacobian subset whose image loses
    only a null deficit. The image of the omitted SOURCE
    points is not asserted null: duplicate fibres remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanMetricCompleteness EuclideanMetricSeparability
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianChartReference RiemannianChartLift RiemannianReferenceSetImage
  RiemannianMapDifferential RiemannianMapDifferentialLocal RiemannianMapJacobian
  RiemannianLinearJacobian RiemannianJacobianRank RiemannianHausdorffNullEquivalence
  BorelAreaSelection InjectiveDifferentialPieceUP NormDifferentialUP
  PartialFunctionUP TopologicalBorel ContinuousBorelPreimages InjectiveBorelImage
  NormMetricScaleContinuity LipschitzUP RealHausdorffMeasure HausdorffMeasure
  MeasureUP MeasureAlmostBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_riemannian_area_locus]: the
    actual positive original-map Jacobian locus, extending
    3.2.4, p. 244, as required in 3.2.46,
    p. 282. Undefined differential points are excluded. *)
Definition positive_riemannian_area_locus (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :=
  [set x | exists j, partial_function_graph (riemannian_map_jacobian f m) x j /\ 0<j].

(** Source for [riemannian_local_borel_area_selection]:
    the actual local Borel univalent selection with positive
    original Jacobian, supporting 3.2.46, p. 282,
    via 3.2.4, p. 244. Local coordinate extension
    hypotheses are discharged by the original path-Lipschitz
    theorem in the global application. The original source
    need only be completed measurable; its image deficit,
    rather than all omitted source images, is null. *)
Theorem riemannian_local_borel_area_selection (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (F : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hRange : forall z, B (F z)) (hp : 0<=m%:R :> R)
    (S : set (riemannian_metric_space hg)) :
  open U -> U `<=` A -> is_metric_lipschitz setT F ->
  (forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x)) ->
  measure_measurable (@riemannian_chart_reference R m A g hg) S ->
  (forall x, S x -> U (val x)) ->
  exists W : set (riemannian_metric_space hg),
    borel_set W /\ W `<=` S `&` positive_riemannian_area_locus f /\
    (forall x y, W x -> W y -> f x=f y -> x=y) /\
    borel_set (f @` W) /\
    riemannian_hausdorff_measure hh m%:R hp ((f @` S) `\` (f @` W))=0%E.
Proof.
move=> hU hUA hFLip hAgreement hS hSU.
pose X := [the topologicalType of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose T := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose v := fun x : X=>(val x : E).
pose w := fun y : Y=>(val y : T).
pose Z := v @` S.
pose G := @riemannian_chart_lift R E n B h hh F hRange.
have hZ := @riemannian_reference_coordinate_image_measurable R m A g hg S hS.
have [C [hC [hCZ [hCInj hNull]]]] := euclidean_borel_area_selection hFLip hZ.
pose W : set X := v @^-1` C.
have hW : borel_set W.
  exact (@continuous_borel_preimage X E v
    (@riemannian_chart_inclusion_continuous R m A g hg) C hC).
have hWS x (hx : W x) : S x.
  have [z hz hEq] := (hCZ (val x) hx).1.
  have hzx : z=x := val_inj hEq; by rewrite -hzx.
have hPoint x (hx : S x) : G (v x)=f x.
  apply: val_inj; exact: hAgreement x (hSU x hx).
have hWPositive x (hx : W x) : positive_riemannian_area_locus f x.
  have hPositive := (hCZ (val x) hx).2.
  rewrite positive_jacobian_injective_locus in hPositive.
  have [D [hD hInj]] := hPositive.
  have hActualD := (@riemannian_map_differential_local_coordinates R m n A B g h hg hh f U F
    hU hUA hAgreement x (hSU x (hWS x hx)) D).2 hD.
  pose j := riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP x))
    (riemannian_tensor_inner hh (set_valP (f x))) m D.
  exists j; split.
  - apply: (@riemannian_map_jacobian_graph R m n A B g h hg hh f m x j).2.
    exists D; split; last by [].
    exact: (riemannian_map_differential_graph f x D).1 hActualD.
  - exact: (@riemannian_area_jacobian_positive_iff_injective R m n
      (g (val x)) (h (val (f x))) (riemannian_tensor_inner hg (set_valP x))
      (riemannian_tensor_inner hh (set_valP (f x))) D).2 hInj.
have hImage : f @` W=G @` C.
  apply/seteqP; split=> y.
  - move=> [x hx <-]; exists (val x); first exact hx; exact: hPoint x (hWS x hx).
  - move=> [z hz <-]; have [x hx hxz] := (hCZ z hz).1.
    exists x.
    + change (C (val x)); by rewrite hxz.
    + by rewrite -hxz hPoint.
have hGCont : continuous G.
  apply: (@riemannian_chart_lift_continuous R E n B h hh F hRange).
  have [K [hK hBound]] := hFLip.
  apply: (@metric_fixed_lipschitz_continuous R E T F K (ltW hK)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hImageBorel : borel_set (f @` W).
  rewrite hImage.
  apply: (@injective_borel_image_borel R E Y G C (@euclidean_metric_complete R m)
    (@euclidean_metric_separable R m) (@metric_hausdorff R Y) hGCont hC).
  move=> x y hx hy hEq; exact: hCInj x y hx hy (congr1 w hEq).
exists W; split; first exact hW; split.
- move=> x hx; split; [exact: hWS x hx | exact: hWPositive x hx].
split.
- move=> x y hx hy hEq.
  have hFValue : F (val x)=F (val y).
    rewrite (hAgreement x (hSU x (hWS x hx))) (hAgreement y (hSU y (hWS y hy))).
    exact (congr1 (fun z : Y=>val z) hEq).
  have hVal : val x=val y := @hCInj (val x) (val y) hx hy hFValue.
  exact: val_inj hVal.
split; first exact hImageBorel.
apply: (@riemannian_hausdorff_null_iff R n B h hh m%:R hp ((f @` S) `\` (f @` W))).2.
rewrite real_hausdorff_measure_natural.
apply: (@measure_null_subset R T (@hausdorff_measure R T m)
  (@hausdorff_measure_is_measure R T m) _ ((F @` Z) `\` (F @` C)) _ hNull).
move=> z [y [[x hx hxy] hNot] <-]; split.
- exists (val x); first by exists x.
  by rewrite (hAgreement x (hSU x hx)) hxy.
- move=> [q hq hQy].
  have [x' hx' hxq] := (hCZ q hq).1.
  apply: hNot; exists x'.
  + change (C (val x')); by rewrite hxq.
  + apply: val_inj.
    by rewrite -(hAgreement x' (hSU x' hx')) hxq.
Qed.
