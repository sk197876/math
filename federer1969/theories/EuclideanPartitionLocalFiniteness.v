(** Federer (1969), 3.1.13, p. 225:
    the tenfold selected balls, and hence
    every subordinate support family, are locally
    finite on the original open-cover union. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalFiniteness.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Variable Phi : set (set X).
Variable S : set X.
Hypothesis ho : forall T, Phi T -> open T.
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).

(** Source for [partition_tenfold_balls_locally_finite]:
    the local finiteness assertion in Federer
    3.1.13, p. 225. The open
    ball of radius 10h(x) meets only
    the finite family S_x from p. 224. *)
Theorem partition_tenfold_balls_locally_finite :
  is_locally_finite_family_on U S (fun s=>metric_closed_ball s (10*h s)).
Proof.
move=>x hx.
have hp : 0<h x.
  apply: (federer_cover_radius_positive ho).
  have [T hT hxT] := hx; by exists T.
have hr : 0<10*h x by rewrite mulr_gt0 // ltr0n.
exists [set y | mdist x y<10*h x].
split; first exact: metric_open_ball_open.
split; first by rewrite /= mdistxx.
apply: (sub_finite_set _ (partition_ball_overlap_finite hS hx)).
move=>s [hs [y [hy hsy]]].
split; first exact hs.
exists y; split; [exact: ltW hy|exact hsy].
Qed.

(** Source for [partition_subordinate_supports_locally_finite]:
    supports contained in the tenfold balls
    form a locally finite family on the
    open union, as asserted for the
    partition functions in Federer 3.1.13, p. 225. *)
Theorem partition_subordinate_supports_locally_finite (K : X->set X) :
  (forall s, S s -> K s `<=` metric_closed_ball s (10*h s)) ->
  is_locally_finite_family_on U S K.
Proof.
move=>hK; exact: (locally_finite_family_subsets hK partition_tenfold_balls_locally_finite).
Qed.
End LocalFiniteness.
