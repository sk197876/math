(** Federer (1969), 3.1.13, pp. 224–225:
    abstract laws for the selected ball cover
    underlying the partition of unity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets
  cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FedererCoverRadius LipschitzRadiusOverlap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BallCoverSpecification.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Variable Phi : set (set X).
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).

(** Source for [is_federer_partition_ball_cover]:
    the selected centers S and their
    geometric properties in Federer 3.1.13,
    pp. 224–225. These laws are
    proved together before the smooth bumps
    are attached to the selected balls. *)
Record is_federer_partition_ball_cover (S : set X) : Prop := {
  (** Source for [partition_ball_centers_in_domain]:
      S is contained in the open-cover
      union, Federer 3.1.13, p. 224. *)
  partition_ball_centers_in_domain : S `<=` U;
  (** Source for [partition_ball_centers_countable]:
      S is countable, Federer 3.1.13, p. 224. *)
  partition_ball_centers_countable : countable S;
  (** Source for [partition_original_balls_disjoint]:
      the closed balls of radius h(s)
      are disjoint, Federer 3.1.13, p. 224. *)
  partition_original_balls_disjoint : forall s t, S s -> S t -> s<>t ->
    metric_closed_ball s (h s) `&` metric_closed_ball t (h t)=set0;
  (** Source for [partition_fivefold_balls_cover]:
      the fivefold balls cover exactly the
      union of the original open family,
      Federer 3.1.13, p. 224. *)
  partition_fivefold_balls_cover :
    (\bigcup_(s in S) metric_closed_ball s (5*h s))=U;
  (** Source for [partition_tenfold_balls_subordinate]:
      the eventual bump supports refine the
      original family, Federer 3.1.13,
      pp. 224–225. *)
  partition_tenfold_balls_subordinate : forall s, S s ->
    exists T, Phi T /\ metric_closed_ball s (10*h s) `<=` T;
  (** Source for [partition_ball_overlap_finite]:
      every S_x is finite, as follows
      from 3.1.12 in the application on
      Federer 3.1.13, p. 224. *)
  partition_ball_overlap_finite : forall x, U x ->
    finite_set (lipschitz_radius_overlap S h 10 10 x);
  (** Source for [partition_ball_overlap_bound]:
      the exact bound card(S_x)<=129^m
      on Federer 3.1.13, p. 224. *)
  partition_ball_overlap_bound : forall x, U x ->
    ((#|` fset_set (lipschitz_radius_overlap S h 10 10 x)|)%:R : R)<=129^+m;
  (** Source for [partition_ball_radius_ratios]:
      neighboring selected radii differ by
      at most a factor three, Federer
      3.1.13, p. 224, from 3.1.12. *)
  partition_ball_radius_ratios : forall x, U x -> forall s,
    lipschitz_radius_overlap S h 10 10 x s ->
    1/3<=h x/h s<=3
}.
End BallCoverSpecification.
