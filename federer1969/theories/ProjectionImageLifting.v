(** Supporting openness argument for Federer (1969), 2.10.5(2), p. 173,
    projection-volume continuity. An orthogonal projection has an isometric
    right inverse by 1.7.4, p. 30. Hence a target displacement can be lifted
    with exactly the same length. No continuously chosen family of right
    inverses is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalInjectionSpaces
  OrthogonalMaps AdjointUP AdjointCriteria.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_projection_exact_distance_lift]:
    supporting right-inverse consequence of Federer
    1.7.4, p. 30, for continuity in 2.10.5(2),
    p. 173. Lift y by x+g(y-p(x)), where
    g is an isometric right inverse of p. *)
Lemma orthogonal_projection_exact_distance_lift (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m)
    (x : inner_metric_space (@euclidean_inner_productP R n))
    (y : inner_metric_space (@euclidean_inner_productP R m)) :
  exists z : inner_metric_space (@euclidean_inner_productP R n),
    euclidean_projection_linear p z=y /\
    mdist x z=mdist (euclidean_projection_linear p x : inner_metric_space (@euclidean_inner_productP R m)) y.
Proof.
have [g [hg hadj]] := orthogonal_projection_map_projection p.
have hright : cancel g (euclidean_projection_linear p).
  exact: (@orthogonal_iff_adjoint_left_inverse R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) g (euclidean_projection_linear p) hadj).1 hg.
exists (x+g (y-euclidean_projection_linear p x)); split.
- by rewrite linearD hright addrC subrK.
- rewrite inner_metric_distanceE opprD addrA subrr add0r inner_normN.
  rewrite (@orthogonal_map_norm R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) g hg).
  by rewrite inner_metric_distanceE -[euclidean_projection_linear p x-y]opprB inner_normN.
Qed.
