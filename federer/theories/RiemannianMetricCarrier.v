(** Federer (1969), 3.2.46, p. 281: a finite metric
    carrier for the actual chart domain, using min(1,rho).
    This technical adapter retains the original path infimum
    separately and agrees with it at every distance below one.
    Infinite distances between components are not declared finite. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianDistance RiemannianDistanceBasic
  RiemannianDistanceSymmetry RiemannianDistanceTriangle RiemannianDistancePositive
  ExtendedRealUnitCap ExtendedRealUnitCapOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_metric_space]: the actual subtype
    A as a finite metric carrier supporting 3.2.46, p. 281.
    Its topology is built from the capped path distance; agreement
    with the original chart topology is a separate theorem. *)
Definition riemannian_metric_space (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) g
    (hg : @is_continuous_riemannian_tensor R n A g) : Type := set_type A.
HB.instance Definition _ (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :=
  Choice.copy (riemannian_metric_space hg) (set_type A).

Section Carrier.
Context (R : realType) n A g (hg : @is_continuous_riemannian_tensor R n A g).
Local Notation M := (riemannian_metric_space hg).

(** Source for [riemannian_metric_distance]: capped original
    curve distance on the actual chart points, technical metric
    support for 3.2.46, p. 281. The cap is opaque and its
    laws, rather than its private construction, are used. *)
Definition riemannian_metric_distance (x y : M) : R :=
  extended_real_unit_cap (@riemannian_distance R n A g (val x) (val y)).

(** Source for [riemannian_metric_distance_self]: the zero
    diagonal law of the technical finite carrier supporting
    the metric assertion of 3.2.46, p. 281. *)
Lemma riemannian_metric_distance_self x : riemannian_metric_distance x x = 0.
Proof.
rewrite /riemannian_metric_distance
  (@riemannian_distance_self R n A g hg (val x) (set_valP x)).
exact: extended_real_unit_cap_zero.
Qed.

(** Source for [riemannian_metric_distance_separates]: the
    original separation theorem proves separation in the finite
    carrier, supporting 3.2.46, p. 281. *)
Lemma riemannian_metric_distance_separates x y :
  riemannian_metric_distance x y = 0 -> x = y.
Proof.
move=> hZero; apply: val_inj.
have hOriginal : @riemannian_distance R n A g (val x) (val y) = 0%E.
  apply/eqP; rewrite -(extended_real_unit_cap_zero_iff
    (@riemannian_distance_nonnegative R n A g (val x) (val y))).
  by apply/eqP.
exact: (@riemannian_distance_separates R n A g hg (val x) (val y) (set_valP x) hOriginal).
Qed.

(** Source for [riemannian_metric_distance_symmetric]:
    the actual curve reversal theorem supplies symmetry of
    the finite carrier, supporting 3.2.46, p. 281. *)
Lemma riemannian_metric_distance_symmetric x y :
  riemannian_metric_distance x y = riemannian_metric_distance y x.
Proof.
by rewrite /riemannian_metric_distance
  (@riemannian_distance_symmetric R n A g hg (val x) (val y)).
Qed.

(** Source for [riemannian_metric_distance_triangle]: the
    actual curve triangle theorem and proved scalar cap laws
    give the finite metric triangle, supporting 3.2.46, p. 281. *)
Lemma riemannian_metric_distance_triangle y x z :
  riemannian_metric_distance x z <=
    riemannian_metric_distance x y + riemannian_metric_distance y z.
Proof.
have hXY := @riemannian_distance_nonnegative R n A g (val x) (val y).
have hYZ := @riemannian_distance_nonnegative R n A g (val y) (val z).
have hXZ := @riemannian_distance_nonnegative R n A g (val x) (val z).
have hTriangle := @riemannian_distance_triangle R n A g hg (val x) (val y) (val z).
exact: le_trans (extended_real_unit_cap_monotone hXZ (adde_ge0 hXY hYZ) hTriangle)
  (extended_real_unit_cap_subadditive hXY hYZ).
Qed.

HB.instance Definition _ := isMetric.Build R M
  riemannian_metric_distance_self riemannian_metric_distance_separates
  riemannian_metric_distance_symmetric riemannian_metric_distance_triangle.

(** Source for [riemannian_metric_distanceE]: the finite
    carrier exposes exactly the capped original distance,
    technical support for 3.2.46, p. 281. *)
Lemma riemannian_metric_distanceE (x y : M) :
  mdist x y = extended_real_unit_cap (@riemannian_distance R n A g (val x) (val y)).
Proof. by []. Qed.

(** Source for [riemannian_metric_small_ball]: balls at
    radii below one retain the exact original rho test,
    technical support for local metric and Hausdorff arguments
    in 3.2.46, p. 281. *)
Lemma riemannian_metric_small_ball (x y : M) (r : R) :
  r < 1 -> (mdist x y < r) = (@riemannian_distance R n A g (val x) (val y) < r%:E)%E.
Proof.
move=> hr; rewrite riemannian_metric_distanceE.
exact: extended_real_unit_cap_small_ball (riemannian_distance_nonnegative A g (val x) (val y)) hr.
Qed.

(** Source for [riemannian_metric_small_distance]: original
    distances at most one agree exactly with the finite
    carrier, technical support for 3.2.46, p. 281. *)
Lemma riemannian_metric_small_distance (x y : M) :
  (@riemannian_distance R n A g (val x) (val y) <= 1)%E ->
  (mdist x y)%:E = @riemannian_distance R n A g (val x) (val y).
Proof.
move=> hSmall; rewrite riemannian_metric_distanceE.
apply: extended_real_unit_cap_small_value; by apply/andP; split=> //; exact: riemannian_distance_nonnegative.
Qed.
End Carrier.
