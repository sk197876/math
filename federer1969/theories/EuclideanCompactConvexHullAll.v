(** Supporting laws for Federer (1969), 4.1.16, p. 374:
    the convex hull of a compact current support is compact,
    including the zero current's empty support. The earlier
    compact-hull theorem already proves the nonempty case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric InnerConvex ConvexHull
  InnerCompactConvexHull InnerNorm RealNormUP NormMetric HilbertFormCompactness
  FiniteNormCompactHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [convex_hull_empty]: supporting the empty
    support case of Federer 4.1.16, p. 374. The least
    convex-superset laws identify the hull of the empty set
    with the empty set; no point is chosen. *)
Lemma convex_hull_empty (R : realFieldType) (V : lmodType R) :
  @convex_hull R V set0=set0.
Proof.
apply/seteqP; split; last by move=> x [].
apply: (@convex_hull_least R V set0 set0).
- by move=> x [].
- by move=> x y [].
Qed.

(** Source for [euclidean_compact_convex_hull_all]: the
    convex hull of the original compact support is compact,
    supporting Federer 4.1.16, p. 374, by the finite-norm
    compact-hull result from 2.10.21, p. 184. Empty sets
    and dimension zero require no inhabitance premise. *)
Theorem euclidean_compact_convex_hull_all (R : realType) n
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> compact (@convex_hull R (R_n R n) K :
    set (inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=> hCompact.
case: (pselect (K !=set0)) => [hNonempty|hEmpty].
- exact: (@inner_compact_convex_hull R (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) K (@coordinate_basisP R n)
    hCompact hNonempty).
- have hZero : K=set0.
    apply/seteqP; split; last by move=> x [].
    move=> x hx; exfalso; apply: hEmpty; by exists x.
  rewrite hZero convex_hull_empty; exact: compact0.
Qed.

(** Source for [euclidean_own_norm_compact_convex_hull_all]:
    the same literal compact hull in the norm topology of
    actual current supports, supporting Federer 4.1.16,
    p. 374. Apply the preceding arbitrary-norm theorem
    with the Euclidean norm; no topology conversion or
    nonempty-current premise is added. *)
Theorem euclidean_own_norm_compact_convex_hull_all (R : realType) n
    (K : set (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))) :
  compact K -> compact (@convex_hull R (R_n R n) K :
    set (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))).
Proof.
move=> hCompact.
case: (pselect (K !=set0)) => [hNonempty|hEmpty].
- exact: (@finite_norm_compact_convex_hull R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    n (@coordinate_basis R n) K (@coordinate_basisP R n)
    hCompact hNonempty).
- have hZero : K=set0.
    apply/seteqP; split; last by move=> x [].
    move=> x hx; exfalso; apply: hEmpty; by exists x.
  rewrite hZero convex_hull_empty; exact: compact0.
Qed.
