(** Federer (1969), 2.10.46, p. 203: consequences of orthogonal coordinates
    adapted to p for the Fubini estimate. Work only from the abstract chart
    laws, before proving existence. Source context:
    EuclideanRightBlockProjection.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric OrthogonalMaps
  EuclideanRightBlockProjection EuclideanBlockCoordinates OrthogonalProjectionChartUP
  EuclideanLebesgueDimensions EuclideanLebesgueLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_chart_backward_orthogonal]: supporting
    inverse isometry for the orthogonal change of
    coordinates in 2.10.46, p. 203. It follows
    from the forward isometry and inverse laws. *)
Lemma projection_chart_backward_orthogonal (R : realType) m k p f g :
  @is_orthogonal_projection_chart R m k p f g ->
  is_orthogonal_map (@euclidean_inner_product R (m+k)) (@euclidean_inner_product R (m+k)) g.
Proof.
move=> hc; exact: orthogonal_inverse (projection_chart_orthogonal_law hc)
  (projection_chart_backward_inverse_law hc).
Qed.

(** Source for [projection_chart_fibre_coordinate]: supporting
    coordinate identification of projection fibres in
    the Fubini step of 2.10.46, p. 203.
    The first block parametrises each fibre. *)
Lemma projection_chart_fibre_coordinate (R : realType) m k p f g :
  @is_orthogonal_projection_chart R m k p f g -> forall x y,
    p (g (@euclidean_block_join R m k (x,y)))=y.
Proof.
move=> hc x y.
by rewrite -(projection_chart_coordinate_law hc) (projection_chart_backward_inverse_law hc)
  euclidean_right_block_pair.
Qed.

(** Source for [projection_chart_volume]: supporting
    preservation of volume under the orthogonal coordinates
    used with Fubini in 2.10.46, p. 203,
    by the invariance in 2.7.16, p. 135.
    Arbitrary, including nonmeasurable, targets are permitted. *)
Lemma projection_chart_volume (R : realType) m k p f g :
  @is_orthogonal_projection_chart R m k p f g ->
  forall S : set (inner_metric_space (@euclidean_inner_productP R (m+k))),
    euclidean_lebesgue_measure (m+k) (f @` S)=euclidean_lebesgue_measure (m+k) S.
Proof.
move=> hc S.
have he : f @` S=g @^-1` S.
  apply/seteqP; split=> x.
  - move=> [y hy <-]; by rewrite /= (projection_chart_forward_inverse_law hc).
  - move=> hx; exists (g x); first exact hx.
    exact (projection_chart_backward_inverse_law hc x).
rewrite he.
exact: (@euclidean_orthogonal_pushforward R (m+k) g
  (projection_chart_backward_orthogonal hc) S).
Qed.
