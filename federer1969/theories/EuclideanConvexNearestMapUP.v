(** Federer (1969), 4.1.16, pp. 373-374:
    the nearest-point map is specified by the preceding
    independent minimising laws. Its existence, range,
    fixed-point and Lipschitz properties are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric InnerConvex InnerNearestUP InnerNearestContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_convex_nearest_map]: the map
    x to its nearest point in C, Federer 4.1.16,
    p. 373. The same nearest-point specification was
    proved earlier in 1.7.13, p. 37. No existence or
    contraction conclusion is part of this definition. *)
Definition is_euclidean_convex_nearest_map (R : realType) n
    (C : set (R_n R n)) (P : R_n R n -> R_n R n) : Prop :=
  forall x,
    is_inner_nearest (@euclidean_inner_productP R n) x C (P x).

(** Source for [euclidean_convex_nearest_map_unique]: the
    displayed relation is a function, Federer 4.1.16,
    p. 373. The preceding nearest-pair contraction law
    proves uniqueness at a common source point without
    assuming a constructed projection. *)
Theorem euclidean_convex_nearest_map_unique (R : realType) n
    (C : set (R_n R n)) (P Q : R_n R n -> R_n R n) :
  is_inner_convex C ->
  is_euclidean_convex_nearest_map C P ->
  is_euclidean_convex_nearest_map C Q -> P = Q.
Proof.
move=> hC hP hQ; apply: funext => x.
have hBound := @inner_nearest_pair_nonexpanding R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  C x x (P x) (Q x) hC (hP x) (hQ x).
rewrite subrr inner_norm0 in hBound.
have hZero : inner_norm (@euclidean_inner_productP R n) (P x-Q x)=0.
  by apply/le_anti; rewrite hBound inner_norm_nonnegative.
by move/eqP: hZero; rewrite inner_norm_eq0 subr_eq0 => /eqP.
Qed.
