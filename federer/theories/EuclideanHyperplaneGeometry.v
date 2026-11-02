(** Federer (1969), 2.10.47, p. 204: induction on ambient dimension reduces
    a positive hyperplane section to Euclidean space of one lower dimension.
    The maps below are compositions of the existing abstract normal chart
    and public head/tail maps, not a new choice of coordinates. Their
    geometry follows from the chart laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerNorm OrthogonalMaps EuclideanCoordinateSplit EuclideanHeadTailGeometry
  EuclideanNormalChartUP NormalHeadChartGeometry CoordinateProjection OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_tail_nonexpanding]: supporting
    coordinate projection estimate for the dimension reduction
    in 2.10.47, p. 204, by the Pythagorean identity. *)
Lemma euclidean_tail_nonexpanding (R : realType) n
    (x y : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  mdist (@coordinate_tail R n x : inner_metric_space (@euclidean_inner_productP R n))
    (@coordinate_tail R n y)<=mdist x y.
Proof.
rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 // euclidean_head_tail_squared_distance lerDl.
exact: sqr_ge0.
Qed.

(** Source for [euclidean_fixed_head_isometry]: supporting
    isometric embedding of R^n into a coordinate hyperplane
    in 2.10.47, p. 204. *)
Lemma euclidean_fixed_head_isometry (R : realType) n (t : R)
    (x y : inner_metric_space (@euclidean_inner_productP R n)) :
  mdist (@euclidean_join R n (x,t)) (@euclidean_join R n (y,t))=mdist x y.
Proof.
have hh := @euclidean_head_tail_squared_distance R n (@euclidean_join R n (x,t)) (@euclidean_join R n (y,t)).
have hx := @euclidean_joinK R n (x,t); have hy := @euclidean_joinK R n (y,t).
have hxT : coordinate_tail (@euclidean_join R n (x,t))=x := congr1 fst hx.
have hyT : coordinate_tail (@euclidean_join R n (y,t))=y := congr1 fst hy.
have hxH : coordinate_head (@euclidean_join R n (x,t))=t := congr1 snd hx.
have hyH : coordinate_head (@euclidean_join R n (y,t))=t := congr1 snd hy.
rewrite hxT hyT hxH hyH subrr normr0 expr0n addr0 in hh.
apply/eqP; rewrite eq_le; apply/andP; split;
  by rewrite -(ler_sqr _ _) ?nnegrE ?mdist_ge0 // hh.
Qed.

(** Source for [euclidean_orthogonal_distance]: supporting
    metric consequence of the orthogonal chart used in
    2.10.47, p. 204; the norm law is 1.7.2, p. 28. *)
Lemma euclidean_orthogonal_distance (R : realType) n (f : {linear R_n R n -> R_n R n}) :
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) f ->
  forall x y : inner_metric_space (@euclidean_inner_productP R n), mdist (f x : inner_metric_space (@euclidean_inner_productP R n)) (f y)=mdist x y.
Proof.
move=> hf x y; rewrite !inner_metric_distanceE -linearB.
exact: (@orthogonal_map_norm R _ _ _ _ (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R n) f hf (x-y)).
Qed.

Section Hyperplane.
Variables (R : realType) (n : nat) (D : euclidean_normal_chart_data R n.+1) (t : R).
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).

(** Source for [normal_hyperplane_embedding]: derived affine
    slice of the existing normal chart for 2.10.47,
    p. 204. No chart implementation is used. *)
Definition normal_hyperplane_embedding (x : E n) : E n.+1 :=
  normal_chart_forward_map D (@euclidean_join R n (x,t)).

(** Source for [normal_hyperplane_projection]: derived lower
    dimensional coordinates for 2.10.47, p. 204. *)
Definition normal_hyperplane_projection (x : E n.+1) : E n :=
  coordinate_tail (normal_chart_backward_map D x).

Variable u : R_n R n.+1.
Hypothesis hD : @is_euclidean_normal_chart R n.+1 ord0 u D.

(** Source for [normal_hyperplane_embeddingK]: the slice
    has a nonexpanding left inverse, as required to transfer
    its measure in 2.10.47, p. 204. *)
Lemma normal_hyperplane_embeddingK : cancel normal_hyperplane_embedding normal_hyperplane_projection.
Proof.
move=> x; rewrite /normal_hyperplane_embedding /normal_hyperplane_projection
  (normal_chart_forward_inverse_law hD).
exact (congr1 fst (@euclidean_joinK R n (x,t))).
Qed.

(** Source for [normal_hyperplane_embedding_isometry]: distance
    preservation for the affine embedding supporting
    2.10.47, p. 204. *)
Lemma normal_hyperplane_embedding_isometry x y :
  mdist (normal_hyperplane_embedding x) (normal_hyperplane_embedding y)=mdist x y.
Proof.
rewrite /normal_hyperplane_embedding
  (euclidean_orthogonal_distance (normal_chart_orthogonal_law hD)).
exact: euclidean_fixed_head_isometry.
Qed.

(** Source for [normal_hyperplane_projection_nonexpanding]: the
    lower dimensional coordinate projection is nonexpanding,
    supporting both measure comparisons in 2.10.47, p. 204. *)
Lemma normal_hyperplane_projection_nonexpanding x y :
  mdist (normal_hyperplane_projection x) (normal_hyperplane_projection y)<=mdist x y.
Proof.
have hg := orthogonal_inverse (normal_chart_orthogonal_law hD) (normal_chart_backward_inverse_law hD).
have hh := @euclidean_tail_nonexpanding R n (normal_chart_backward_map D x) (normal_chart_backward_map D y).
by rewrite (euclidean_orthogonal_distance hg) in hh.
Qed.

(** Source for [normal_hyperplane_projectionK]: points in the
    indicated hyperplane are recovered from the lower
    dimensional coordinates, 2.10.47, p. 204. *)
Lemma normal_hyperplane_projectionK (x : E n.+1) :
  coordinate_head (normal_chart_backward_map D x)=t ->
  normal_hyperplane_embedding (normal_hyperplane_projection x)=x.
Proof.
move=> ht; rewrite /normal_hyperplane_embedding /normal_hyperplane_projection -ht.
change (normal_chart_forward_map D (@euclidean_join R n (@euclidean_split R n (normal_chart_backward_map D x)))=x).
by rewrite euclidean_splitK (normal_chart_backward_inverse_law hD).
Qed.
End Hyperplane.
