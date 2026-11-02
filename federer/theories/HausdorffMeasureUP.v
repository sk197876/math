(** Federer (1969), 2.10.2(1)–(2), p. 171: specify integer-dimensional
    Hausdorff and spherical measures by the abstract Caratheodory laws with
    the printed normalized diameter gauge. Closed and open generator
    variants are specified independently, before proving their equality.
    Closed balls retain strictly positive real radii from 2.8.1, p. 141;
    singleton diameter zero does not justify using a forbidden radius-zero
    ball. this file concerns the book's initial integer-degree definition.
    No relevant correction in the local Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls HausdorffLengthUP HausdorffDiameterCost
  CaratheodoryLimitUP CaratheodoryLimitUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonempty_open_metric_sets]: direct alternative
    family of nonempty open generators in Federer 2.10.2(1),
    p. 171. Its equality with unrestricted covers is a later
    theorem, not a defining assumption. *)
Definition nonempty_open_metric_sets (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type [set A : set X | open A /\ A !=set0]].

(** Source for [is_positive_metric_closed_ball]: direct closed-
    ball predicate for Federer 2.10.2(2), p. 171, using
    the convention 2.8.1, p. 141. Specify a center and
    a strictly positive real radius through their distance laws. *)
Definition is_positive_metric_closed_ball (R : realType) (X : metricType R) (A : set X) :=
  exists a : X, exists r : R, 0<r /\ forall x, A x <-> mdist a x<=r.

(** Source for [positive_closed_metric_balls]: direct generator
    family of spherical measure in Federer 2.10.2(2), p. 171.
    Membership is the abstract ball predicate, not an arbitrary
    chosen center or radius; representations need not be unique. *)
Definition positive_closed_metric_balls (R : realType) (X : metricType R) : choiceType :=
  [the choiceType of set_type (@is_positive_metric_closed_ball R X)].

(** Source for [positive_metric_closed_ball_nonempty]: supporting
    nonemptiness of every spherical generator in Federer
    2.10.2(2), p. 171, retaining the positive-radius
    convention of 2.8.1, p. 141. *)
Lemma positive_metric_closed_ball_nonempty (R : realType) (X : metricType R) (A : set X) :
  is_positive_metric_closed_ball A -> A !=set0.
Proof.
move=> [a [r [hr hA]]]; exists a; apply/(hA a); rewrite mdistxx; exact: ltW hr.
Qed.

(** Source for [positive_metric_closed_ball_closed]: supporting
    Borel-generator assertion for spherical measure in Federer 2.10.2(2), p.
    171 It follows from the ball's distance laws. *)
Lemma positive_metric_closed_ball_closed (R : realType) (X : metricType R) (A : set X) :
  is_positive_metric_closed_ball A -> closed A.
Proof.
move=> [a [r [hr hA]]].
have he : A=metric_closed_ball a r.
  apply/seteqP; split=> x hx.
  - exact: (hA x).1 hx.
  - exact: (hA x).2 hx.
rewrite he; exact: metric_closed_ball_closed.
Qed.

(** Source for [positive_closed_ball_satisfies_laws]: supporting
    existence of spherical generators in Federer 2.10.2(2),
    p. 171. An actual positive-radius closed ball satisfies
    the abstract predicate; no radius-zero generator is introduced. *)
Lemma positive_closed_ball_satisfies_laws (R : realType) (X : metricType R) (a : X) (r : R) :
  0<r -> is_positive_metric_closed_ball (metric_closed_ball a r).
Proof. move=> hr; exists a,r; split=> // x; by []. Qed.

(** Source for [is_hausdorff_measure]: direct integer-degree
    Hausdorff-measure specification in Federer 2.10.2(1),
    p. 171: apply 2.10.1 with all nonempty subsets and
    the normalized diameter cost. No geometric theorem or
    regularity assertion is assumed in this definition. *)
Definition is_hausdorff_measure (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :=
  @is_caratheodory_limit R X (@nonempty_metric_sets R X)
    (fun A => val A) (fun A => hausdorff_diameter_cost m (val A)) mu.

(** Source for [is_closed_hausdorff_measure]: independent
    closed-cover alternative in Federer 2.10.2(1), p. 171;
    equality with the unrestricted specification is to be proved. *)
Definition is_closed_hausdorff_measure (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :=
  @is_caratheodory_limit R X (@nonempty_closed_metric_sets R X)
    (fun A => val A) (fun A => hausdorff_diameter_cost m (val A)) mu.

(** Source for [is_open_hausdorff_measure]: independent
    open-cover alternative in Federer 2.10.2(1), p. 171.
    The preliminary approximations need not coincide; the
    asserted equality concerns the final measures. *)
Definition is_open_hausdorff_measure (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :=
  @is_caratheodory_limit R X (@nonempty_open_metric_sets R X)
    (fun A => val A) (fun A => hausdorff_diameter_cost m (val A)) mu.

(** Source for [is_spherical_measure]: direct integer-degree
    spherical-measure specification in Federer 2.10.2(2),
    p. 171. Use all closed balls of strictly positive real
    radius, under the convention referred to in 2.8.1. *)
Definition is_spherical_measure (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) :=
  @is_caratheodory_limit R X (@positive_closed_metric_balls R X)
    (fun A => val A) (fun A => hausdorff_diameter_cost m (val A)) mu.

(** Source for [hausdorff_measure_unique]: supporting uniqueness
    of the measure defined by Federer 2.10.2(1), p. 171,
    from the already proved abstract Caratheodory uniqueness. *)
Lemma hausdorff_measure_unique (R : realType) (X : metricType R) (m : nat)
    (mu nu : set X -> \bar R) :
  is_hausdorff_measure m mu -> is_hausdorff_measure m nu -> forall A, mu A=nu A.
Proof. exact: caratheodory_limit_unique. Qed.

(** Source for [spherical_measure_unique]: supporting uniqueness
    of the measure defined by Federer 2.10.2(2), p. 171,
    independently of the later comparison with Hausdorff measure. *)
Lemma spherical_measure_unique (R : realType) (X : metricType R) (m : nat)
    (mu nu : set X -> \bar R) :
  is_spherical_measure m mu -> is_spherical_measure m nu -> forall A, mu A=nu A.
Proof. exact: caratheodory_limit_unique. Qed.
