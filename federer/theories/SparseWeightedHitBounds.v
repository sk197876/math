(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import SparseBallCoverSequenceUP SparseBallCoverRadii WeightedHitMeasure
  MetricClosedBalls MetricSetSeparationInfimum ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sparse_weighted_hit_target_null]: direct
    psi(T)=0 in Federer 2.9.18(1), p. 163.
    No center lies on T, so no positive coefficient
    enters the weighted-hit value of T. *)
Lemma sparse_weighted_hit_target_null (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> weighted_hit_measure c S T=0%E.
Proof.
move=> h; apply/eqP; rewrite eq_le weighted_hit_measure_nonnegative andbT.
apply: extended_real_sup_least=> y [->|[n [x [hx [hs _]]]]]; first exact: lexx.
exfalso; exact (@sparse_cover_centers_outside R X T c S h n x hs hx).
Qed.

(** Source for [sparse_weighted_hit_le_one]: supporting finite
    upper bound for psi in Federer 2.9.18(1), p. 163.
    All coefficients are at most the initial radius one;
    no regularity or additivity beyond the outer-measure laws
    is inferred from this finite total value. *)
Lemma sparse_weighted_hit_le_one (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall A, (weighted_hit_measure c S A<=1)%E.
Proof.
move=> h A; apply: extended_real_sup_least=> y [->|[n [x [_ [_ ->]]]]]; first exact: lee01.
by rewrite lee_fin; exact: sparse_cover_radii_le_one h n.
Qed.

(** Source for [sparse_scaled_radius_below_current]: supporting
    upper endpoint of the oscillating radius interval in
    Federer 2.9.18(1), p. 163. The endpoint
    (n+1)c_(n+1) lies strictly below c_n. *)
Lemma sparse_scaled_radius_below_current (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n, ((n.+1)%:R*c n.+1)%R<c n.
Proof.
move=> h n; have hh := lt_trans (sparse_cover_separation_lower h n) (sparse_cover_separation_upper h n).
by move: hh; rewrite lte_fin.
Qed.

(** Source for [sparse_scaled_radii_decreasing]: supporting
    ordering of the earlier exclusion radii in Federer
    2.9.18(1), p. 163. The scaled endpoints
    (n+1)c_(n+1) themselves decrease strictly, which ensures
    an oscillation ball misses every earlier finite center set. *)
Lemma sparse_scaled_radii_decreasing (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n,
    ((n.+2)%:R*c n.+2)%R<((n.+1)%:R*c n.+1)%R.
Proof.
move=> h n; apply: lt_le_trans (sparse_scaled_radius_below_current h n.+1) _.
have hn : (1<=((n.+1)%:R : R)) by rewrite ler1n.
have hm := ler_wpM2r (ltW (sparse_cover_radius_positive h n.+1)) hn.
by rewrite mul1r in hm.
Qed.

(** Source for [sparse_scaled_radii_antitone]: supporting
    comparison with all earlier exclusion radii in Federer
    2.9.18(1), p. 163. This uses only the
    proved successive decrease of the scaled endpoints. *)
Lemma sparse_scaled_radii_antitone (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n m, (n<=m)%N ->
    ((m.+1)%:R*c m.+1)%R<=((n.+1)%:R*c n.+1)%R.
Proof.
move=> h n m hnm.
have hall k : (((n+k).+1)%:R*c (n+k).+1)%R<=((n.+1)%:R*c n.+1)%R.
  elim: k=> [|k ih]; first by rewrite addn0.
  rewrite addnS.
  exact: le_trans (ltW (sparse_scaled_radii_decreasing h (n+k))) ih.
have he : (n+(m-n)=m)%N by rewrite addnC subnK.
by rewrite -he; exact: hall (m-n)%N.
Qed.
