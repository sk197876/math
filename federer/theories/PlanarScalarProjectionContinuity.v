(** Federer (1969), 3.3.20, p. 307: continuity of the actual scalar projection. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  MetricCartesianProductUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_scalar_original_projection_continuous]: the
    actual original projection used in 3.3.20, p. 307, is continuous.
    The proof gives the explicit Lipschitz bound |u|+|v| from the
    actual coordinate nonexpansion laws; no unit-direction premise is needed. *)
Theorem planar_scalar_original_projection_continuous (R:realType) (u v:R):
  continuous (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p):real_line_metric R).
Proof.
apply:(@metric_fixed_lipschitz_continuous R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
  [the metricType R of real_line_metric R] _ (`|u|+`|v|) (addr_ge0 (normr_ge0 _) (normr_ge0 _))).
move=>x y;rewrite real_line_metric_distanceE.
have hX: `|euclidean_real_plane_first x-euclidean_real_plane_first y|<=mdist x y.
  have h:=(metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 x y Logic.I Logic.I.
  by rewrite mul1r real_line_metric_distanceE in h.
have hY: `|euclidean_real_plane_second x-euclidean_real_plane_second y|<=mdist x y.
  have h:=(metric_product_second_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 x y Logic.I Logic.I.
  by rewrite mul1r real_line_metric_distanceE in h.
have hDifference:(u * euclidean_real_plane_first x+v * euclidean_real_plane_second x)-
    (u * euclidean_real_plane_first y+v * euclidean_real_plane_second y)=
    u * (euclidean_real_plane_first x-euclidean_real_plane_first y)+
    v * (euclidean_real_plane_second x-euclidean_real_plane_second y) by ring.
rewrite hDifference.
apply:le_trans (ler_normD _ _) _.
rewrite !normrM mulrDl.
exact:lerD (ler_wpM2l (normr_ge0 u) hX) (ler_wpM2l (normr_ge0 v) hY).
Qed.
