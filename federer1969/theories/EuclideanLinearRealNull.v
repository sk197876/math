(** Federer (1969), 3.2.46, pp. 281–282: local
    linear chart changes preserve Hausdorff null sets in
    every real degree. Finite operator norms and the proved
    real-degree covering estimate supply the actual comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric OperatorNorm EuclideanLinearMaps
  LipschitzUP RealPowerPositiveLipschitz RealHausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_positive_linear_metric_bound]:
    a finite positive Lipschitz bound for each actual linear
    map, supporting 3.2.46, pp. 281–282. The local bound
    is proved from 1.7.6, p. 33, also for zero maps and n=0. *)
Lemma euclidean_positive_linear_metric_bound (R : realType) n
    (L : {linear R_n R n -> R_n R n}) :
  exists K : R, 0<K /\
    @is_metric_lipschitz_bound R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT L K.
Proof.
pose hE := @euclidean_inner_productP R n.
pose c := linear_operator_norm hE hE (@coordinate_basisP R n) L.
have hc : 0<=c := linear_operator_norm_nonnegative hE hE (@coordinate_basisP R n) L.
have hK : 0<c+1 by lra.
exists (c+1); split; first exact hK; split; first exact: ltW hK.
move=> x y _ _; rewrite !inner_metric_distanceE -linearB.
apply: le_trans (linear_operator_norm_bound hE hE (@coordinate_basisP R n) L (x-y)) _.
apply: ler_wpM2r; first exact: inner_norm_nonnegative.
by rewrite lerDl ler01.
Qed.

(** Source for [euclidean_linear_real_null_image]: a linear
    map preserves actual real-degree Hausdorff null sets,
    supporting 3.2.46, pp. 281–282, by 2.10.11, p. 176.
    The original set need not be measurable. *)
Lemma euclidean_linear_real_null_image (R : realType) n
    (L : {linear R_n R n -> R_n R n}) (p : R) (hp : 0<=p)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @real_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp S=0%E ->
  @real_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp (L @` S)=0%E.
Proof.
move=> hNull; have [K [hK hBound]] := euclidean_positive_linear_metric_bound L.
have h := @real_hausdorff_positive_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] L K p hp hK hBound S.
rewrite hNull mule0 in h.
by apply/eqP; rewrite eq_le h (measure_nonnegative
  (@real_hausdorff_measure_is_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp)).
Qed.

(** Source for [euclidean_linear_real_null_iff]: an actual
    linear automorphism preserves and reflects Hausdorff
    nullity in every real degree, supporting 3.2.46,
    pp. 281–282. Its inverse remains a local proof witness. *)
Lemma euclidean_linear_real_null_iff (R : realType) n
    (L : {linear R_n R n -> R_n R n}) (p : R) (hp : 0<=p)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  injective L ->
  (@real_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp (L @` S)=0%E <->
   @real_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp S=0%E).
Proof.
move=> hInj; split; last exact: euclidean_linear_real_null_image.
move=> hNull; have [M [hML hLM]] := euclidean_linear_inverse hInj.
have hImage : M @` (L @` S)=S.
  apply/seteqP; split=> x.
  - move=> [y [z hz <-] <-]; by rewrite hML.
  - move=> hx; exists (L x); first by exists x.
    exact: hML x.
have h := @euclidean_linear_real_null_image R n M p hp (L @` S) hNull.
by rewrite hImage in h.
Qed.
