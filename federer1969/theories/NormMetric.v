(** Federer (1969), 2.2.7, p. 64: the metric on a normed vector space is
    induced by its given norm. This supporting adapter proves the metric
    laws from the abstract norm laws already used in Chapter 1, without an
    inner-product hypothesis. Source context: LipschitzUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_norm_metric_space]: supporting carrier for
    Federer 2.2.7, p. 64: the vector space with the metric of
    its specified norm. The wrapper distinguishes choices of norm. *)
Definition real_norm_metric_space (R : realType) (V : lmodType R)
    (N : V -> R) (_ : is_real_norm N) : Type := V.
HB.instance Definition _ (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) :=
  GRing.Lmodule.copy (real_norm_metric_space hN) V.
Section Metric.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [real_norm_distance]: Federer 2.2.7, p. 64,
    the normed-space distance in the denominator is N(x-y). *)
Definition real_norm_distance (x y : M) := N (x-y).

(** Source for [real_norm_distance_self]: supporting metric law
    for Federer 2.2.7, p. 64: equal points have distance zero. *)
Lemma real_norm_distance_self x : real_norm_distance x x = 0.
Proof. by rewrite /real_norm_distance subrr (real_seminorm_zero hN.1). Qed.

(** Source for [real_norm_distance_separates]: supporting metric
    law for Federer 2.2.7, p. 64: definiteness of the given norm
    implies separation of distinct points by their distance. *)
Lemma real_norm_distance_separates x y : real_norm_distance x y = 0 -> x = y.
Proof. move=> h; apply/eqP; rewrite -subr_eq0; apply/eqP; exact: hN.2 h. Qed.

(** Source for [real_norm_distance_symmetric]: supporting metric
    law for Federer 2.2.7, p. 64: symmetry follows from N(-v)=N(v). *)
Lemma real_norm_distance_symmetric x y : real_norm_distance x y = real_norm_distance y x.
Proof. rewrite /real_norm_distance; exact: (real_seminorm_subtract hN.1 x y). Qed.

(** Source for [real_norm_distance_triangle]: supporting metric
    law for Federer 2.2.7, p. 64: the norm triangle inequality
    applied to x-z=(x-y)+(y-z). *)
Lemma real_norm_distance_triangle y x z :
  real_norm_distance x z <= real_norm_distance x y + real_norm_distance y z.
Proof.
rewrite /real_norm_distance.
have -> : x-z = (x-y)+(y-z) by rewrite addrA subrK.
exact: (@real_seminorm_triangle R V N hN.1 (x-y) (y-z)).
Qed.
HB.instance Definition _ := isMetric.Build R M
  real_norm_distance_self real_norm_distance_separates
  real_norm_distance_symmetric real_norm_distance_triangle.

(** Source for [real_norm_metric_distanceE]: supporting metric
    compatibility for Federer 2.2.7, p. 64: the general topology
    interface uses exactly the prescribed norm distance. *)
Lemma real_norm_metric_distanceE (x y : M) : mdist x y = N (x-y).
Proof. by []. Qed.
End Metric.
