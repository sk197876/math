(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import SparseBallCoverSequenceUP SparseBallCoverRadii SparseWeightedHitBounds
  WeightedHitMeasure MetricClosedBalls MetricSetSeparationInfimum ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sparse_weighted_hit_ball_value]: direct numerator
    value on the oscillation intervals in Federer 2.9.18(1),
    p. 163. For x in T and c_(n+1)<=r<=(n+1)c_(n+1),
    the ball misses every earlier center set, meets S_(n+1),
    and all later coefficients are at most c_(n+1). Thus
    the exact supremum equals c_(n+1), using only the abstract
    sequence laws and not the sealed recursive choice. *)
Theorem sparse_weighted_hit_ball_value (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) (x : X) (n : nat) (r : R) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  (c n.+1<=r<=((n.+1)%:R*c n.+1))%R ->
  weighted_hit_measure c S (metric_closed_ball x r)=(c n.+1)%:E.
Proof.
move=> h hx /andP [hcr hrb]; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_sup_least=> y [->|[j [a [ha [hs ->]]]]].
  + rewrite lee_fin; exact: ltW (sparse_cover_radius_positive h n.+1).
  + case: (leqP j n)=> [hjn|hnj].
    * have hmem : metric_set_cross_distances (S j) T (mdist a x)%:E.
        by exists a; split=> //; exists x.
      have hdist := @extended_real_inf_lower R _ _ hmem.
      have hscaled := @sparse_scaled_radii_antitone R X T c S h j n hjn.
      have hupper : (mdist a x)%:E<=(((j.+1)%:R*c j.+1)%R)%:E.
        rewrite lee_fin (metric_sym a x); exact: le_trans ha (le_trans hrb hscaled).
      have hbad := lt_le_trans (sparse_cover_separation_lower h j) (le_trans hdist hupper).
      by rewrite ltxx in hbad.
    * rewrite lee_fin; exact (@sparse_cover_radii_antitone R X T c S h n.+1 j hnj).
- have [a [hs hnear]] := @sparse_cover_open_balls_cover R X T c S h n.+1 x hx.
  apply: (@weighted_hit_measure_hit R X c S (metric_closed_ball x r) n.+1).
  exists a; split=> //; rewrite /metric_closed_ball /= (metric_sym x a).
  exact: le_trans (ltW hnear) hcr.
Qed.
