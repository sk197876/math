(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricSetSeparationInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_sparse_ball_cover_sequence]: direct laws
    for c_j and S_j in Federer 2.9.18(1), p. 163:
    positive radii starting at one, finite off-target centers
    whose open balls cover T, and the two displayed strict
    separation inequalities. Existence is a separate theorem. *)
Record is_sparse_ball_cover_sequence (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) : Prop := {
  (** Source for [sparse_cover_radius_positive]: direct positivity
      of c_j in Federer 2.9.18(1), p. 163. *)
  sparse_cover_radius_positive : forall n, (0<c n)%R;
  (** Source for [sparse_cover_initial_radius]: direct c_1=1
      in Federer 2.9.18(1), p. 163; local index zero. *)
  sparse_cover_initial_radius : c 0%N= 1%R;
  (** Source for [sparse_cover_centers_finite]: direct finiteness
      of S_j in Federer 2.9.18(1), p. 163. *)
  sparse_cover_centers_finite : forall n, finite_set (S n);
  (** Source for [sparse_cover_centers_outside]: direct S_j
      contained in the complement of T in Federer 2.9.18(1),
      p. 163. *)
  sparse_cover_centers_outside : forall n, S n `<=` ~` T;
  (** Source for [sparse_cover_open_balls_cover]: direct open-ball
      covering of T in Federer 2.9.18(1), p. 163. *)
  sparse_cover_open_balls_cover : forall n x, T x -> exists a,
    S n a /\ (mdist a x<c n)%R;
  (** Source for [sparse_cover_separation_lower]: direct lower
      separation bound j c_(j+1)<dist(S_j,T) in Federer
      2.9.18(1), p. 163. *)
  sparse_cover_separation_lower : forall n,
    (((n.+1)%:R*c n.+1)%R)%:E<metric_set_distance_infimum (S n) T;
  (** Source for [sparse_cover_separation_upper]: direct upper
      separation bound dist(S_j,T)<c_j in Federer 2.9.18(1),
      p. 163. *)
  sparse_cover_separation_upper : forall n, metric_set_distance_infimum (S n) T<(c n)%:E
}.
