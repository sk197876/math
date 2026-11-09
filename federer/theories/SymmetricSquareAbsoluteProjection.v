(** Federer (1969), 3.3.20, p. 307: all signs of actual projection coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct LebesgueScalarMeasure SymmetricSquareScalarProjections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [symmetric_square_absolute_projection_length]: actual
    projection length is unchanged by replacing both coefficients by
    their absolute values, for a square with reflection-symmetric factor,
    as used in 3.3.20, p. 307. Actual coordinate flips, interchange
    and scalar translation invariance prove every sign case. *)
Theorem symmetric_square_absolute_projection_length (R:realType)
    (B:set (real_line_metric R)) (u v:R):
  (forall x,B x <->B (1-x)) ->
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B)=
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      `|u| * euclidean_real_plane_first p+`|v| * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
Proof.
move=>hB.
have hFirst a b:lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      a * euclidean_real_plane_first p+b * euclidean_real_plane_second p) @` euclidean_cantor_product B B)=
    lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      `|a| * euclidean_real_plane_first p+b * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
  case:(leP 0 a)=>ha;first by rewrite (ger0_norm ha).
  have h:=@symmetric_square_projection_flip_length R B (-a) b hB.
  by rewrite opprK -(ltr0_norm ha) in h.
rewrite (hFirst u v) (@square_scalar_projection_swap R B `|u| v) (hFirst v `|u|).
by rewrite (@square_scalar_projection_swap R B `|v| `|u|).
Qed.
