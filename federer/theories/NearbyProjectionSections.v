(** Supporting local section control for Federer (1969), 2.10.5(2), p. 173,
    and the forward compact convex continuity reference 3.2.36, p. 272. If p
    g is the identity, nearby projections q have q g invertible with inverse
    norm at most two. Joint evaluation continuity and a compact unit ball
    give a uniform perturbation bound; the actual inverse follows from the
    proved identity perturbation estimate of 2.7.16, p. 134. No continuous
    choice of inverses is required for this local assertion. Source context
    and the operator-norm context: NearIdentityEuclideanInverse.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  InnerNormedTopology EuclideanProjectionSpace EuclideanAdditiveGroup
  RectangularEuclideanContinuity NearIdentityEuclideanInverse TensorUP
  CompactProjectionEvaluationControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nearby_projection_sections_bounded_inverse]:
    supporting local uniformly bounded lifting
    operator for Federer 2.10.5(2), p. 173,
    and 3.2.36, p. 272. All neighbourhood and
    inverse witnesses are proved to exist in the
    actual relative Hom topology on O*. *)
Theorem nearby_projection_sections_bounded_inverse (R : realType) (n m : nat)
    (p : euclidean_projection_space R n m)
    (g : {linear R_n R m -> R_n R n}) :
  cancel g (euclidean_projection_linear p) ->
  exists V : set (euclidean_projection_space R n m), open V /\ V p /\
    forall q, V q -> exists h : {linear R_n R m -> R_n R m},
      cancel (linear_comp (euclidean_projection_linear q) g) h /\
      cancel h (linear_comp (euclidean_projection_linear q) g) /\
      forall y, inner_norm (@euclidean_inner_productP R m) (h y)<=
        2*inner_norm (@euclidean_inner_productP R m) y.
Proof.
move=> hgp.
pose P := euclidean_projection_space R n m.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
have hg : continuous (g : Y -> X) := @rectangular_euclidean_linear_continuous R m n g.
pose K : set Y := [set u | inner_norm (@euclidean_inner_productP R m) u<=1].
have hK : compact K.
  have he : K=[set u : Y | `|u-(0%R:Y)|<=1].
    apply/seteqP; split=> u; by rewrite /= subr0 inner_norm_topologyE.
  rewrite he; exact: euclidean_closed_ball_compact.
pose D : set X := (g : Y -> X) @` K.
have hD : compact D.
  apply: continuous_compact=> //; apply: continuous_subspaceT; exact hg.
have he : 0<(2:R)^-1 by rewrite invr_gt0 ltr0n.
have [V [hV [hp hcontrol]]] := @compact_projection_evaluation_control R n m D p
  (2:R)^-1 hD he.
exists V; split=> //; split=> // q hq.
apply: near_identity_euclidean_inverse_bound=> u hu.
have huD : D (g u) by exists u.
have hb := hcontrol q (g u) hq huD.
rewrite hgp inner_metric_distanceE -[u-euclidean_projection_linear q (g u)]opprB inner_normN in hb.
exact: ltW hb.
Qed.
