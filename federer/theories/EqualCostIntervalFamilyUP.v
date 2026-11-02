(** Federer (1969), 2.10.28(4), pp. 192–193: abstract specification of
    Phi(J,n), before constructing its intervals. Index i from zero to n-1
    represents the book's i+1. The common length satisfies the equal-cost
    radius laws and the spacing is (d-s)/(n-1). This hypothesis is absent
    from the printed Federer sentence; the degenerate-parent counterexample
    is in CantorSplitRadiusUP.v. Erratum p. 4, book p. 193 line 7, corrects
    the later sum's containment index. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalGaugeGeometry
  MetricDiameter MetricDiameterReal ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_equal_cost_interval_family]: direct
    interval and parameter laws describing Phi(J,n)
    in 2.10.28(4), p. 192. Specialness
    and the constant-three clipped bound are
    consequences to prove, not defining assumptions. *)
Definition is_equal_cost_interval_family (R : realType) (h : R -> R)
    (J : compact_real_intervals R) (n : nat) (F : {fset compact_real_intervals R}) :=
  (2<=n)%N /\ exists a b s t : R,
    val J=(`[a,b] : set (real_line_metric R)) /\ (0<b-a) /\
    is_cantor_split_radius h (b-a) n s /\ t=cantor_split_spacing (b-a) n s /\
    forall S : compact_real_intervals R, S \in F <-> exists i : nat, (i<n)%N /\
      val S=(`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)).

(** Source for [equal_cost_interval_parent_nondegenerate]: supporting
    required parent condition in 2.10.28(4), p. 192, made explicit. *)
Lemma equal_cost_interval_parent_nondegenerate (R : realType) (h : R -> R)
    (J : compact_real_intervals R) n F :
  is_equal_cost_interval_family h J n F ->
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
Proof.
move=> [_ [a [b [s [t [hJ [hd _]]]]]]].
have hab : a<=b by lra.
rewrite hJ (extended_metric_diameter_segment hab); exact hd.
Qed.

(** Source for [equal_cost_interval_family_nonempty]: supporting
    nonemptiness of Phi(J,n) in 2.10.28(4),
    p. 192. Its first positive-length
    interval is a member by the abstract
    family description, without exposing a construction. *)
Lemma equal_cost_interval_family_nonempty (R : realType) (h : R -> R)
    (J : compact_real_intervals R) n F :
  is_equal_cost_interval_family h J n F -> exists S, S \in F.
Proof.
move=> [hn [a [b [s [t [hJ [hd [hs [ht hchar]]]]]]]]].
have hspos := (cantor_split_radius_bounds hs).1.
have hI : is_compact_real_interval (`[a,a+s] : set (real_line_metric R)).
  exists a,(a+s); split=> //; lra.
pose S : compact_real_intervals R := Sub (`[a,a+s] : set (real_line_metric R)) (mem_set hI).
exists S; apply/(hchar S); exists 0%N; split; first exact: leq_trans (leqnSn 1%N) hn.
by rewrite !mul0r !addr0.
Qed.

(** Source for [equal_cost_interval_family_unique]: supporting
    uniqueness of Phi(J,n) specified in
    2.10.28(4), p. 192, by ordered
    parent endpoints and the unique equal-cost
    child length. No chosen implementation is used. *)
Lemma equal_cost_interval_family_unique (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) n F G :
  is_equal_cost_interval_family h J n F -> is_equal_cost_interval_family h J n G -> F=G.
Proof.
move=> [hn [a [b [s [t [hJ [hd [hs [ht hF]]]]]]]]]
  [hn' [a' [b' [s' [t' [hJ' [hd' [hs' [ht' hG]]]]]]]]].
have hab : a<=b by lra.
have hab' : a'<=b' by lra.
have hsub : (`[a,b] : set (real_line_metric R)) `<=` `[a',b'] by rewrite -hJ -hJ'.
have hsub' : (`[a',b'] : set (real_line_metric R)) `<=` `[a,b] by rewrite -hJ -hJ'.
have [ha hb] := (@compact_segment_subset_endpoints R a b a' b' hab).1 hsub.
have [ha' hb'] := (@compact_segment_subset_endpoints R a' b' a b hab').1 hsub'.
have heqa : a'=a by lra.
have heqb : b'=b by lra.
subst a'; subst b'.
have heqs : s'=s := @cantor_split_radius_unique R h hg (b-a) n s' s hs' hs.
have heqt : t'=t by rewrite ht ht' heqs.
rewrite heqs heqt in hG.
apply/fsetP=> S; apply/idP/idP=> hS.
- exact: (hG S).2 ((hF S).1 hS).
- exact: (hF S).2 ((hG S).1 hS).
Qed.
