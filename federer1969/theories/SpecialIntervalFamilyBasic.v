(** Federer (1969), 2.10.28, pp. 191–192: elementary consequences of the
    special-family specification. In particular, a singleton family is
    special for its own interval, starting the corrected single-root
    induction in (3). Federer's erratum p. 4, book p. 192 line 4, supplies
    card(H_0)=1. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP SpecialIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_singleton]: supporting singleton starting
    family for 2.10.28(3), p. 192, with the erratum's single-root hypothesis
    Degenerate roots are allowed. *)
Lemma special_interval_singleton (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) :
  is_special_interval_family h J [fset J].
Proof.
constructor.
- by move=> S /fset1P ->.
- move=> S T /fset1P -> /fset1P ->; by rewrite eqxx.
- by rewrite big_seq_fset1.
- move=> T; rewrite big_mkcond big_seq_fset1.
  case: asboolP=> hsub.
  + exact (@concave_interval_cost_subset R h hg (val J) (val T) (set_valP J) (set_valP T) hsub).
  + exact (@concave_interval_cost_nonnegative R h hg (val T)).
Qed.

(** Source for [special_interval_contained_cost_bound]: direct
    test-interval inequality from the definition of
    special in 2.10.28, p. 191, in
    particular for the root and later descendants. *)
Lemma special_interval_contained_cost_bound (R : realType) (h : R -> R)
    (J T : compact_real_intervals R) (H : {fset compact_real_intervals R}) :
  is_special_interval_family h J H ->
  \sum_(S <- H | `[< val S `<=` val T >]) concave_interval_cost h (val S)<=concave_interval_cost h (val T).
Proof. move=> hH; exact (@special_interval_envelope R h J H hH T). Qed.

(** Source for [special_interval_member_cost_bound]: supporting
    cost bound for a single descendant in
    2.10.28(3), p. 192. Monotonicity of
    h and inclusion in the parent suffice. *)
Lemma special_interval_member_cost_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J S : compact_real_intervals R)
    (H : {fset compact_real_intervals R}) :
  is_special_interval_family h J H -> S \in H ->
  concave_interval_cost h (val S)<=concave_interval_cost h (val J).
Proof.
move=> hH hS.
exact (@concave_interval_cost_subset R h hg (val S) (val J) (set_valP S) (set_valP J) (special_interval_subsets hH hS)).
Qed.

(** Source for [special_interval_restriction_membership]: supporting
    membership law of H intersect {T:T subset S}
    in 2.10.28(3), p. 192. No enumeration
    of the finite family is chosen. *)
Lemma special_interval_restriction_membership (R : realType)
    (H : {fset compact_real_intervals R}) (A : set (real_line_metric R)) S :
  S \in special_interval_restriction H A <-> S \in H /\ val S `<=` A.
Proof.
rewrite /special_interval_restriction in_fset /=; split.
- by move=> /andP [hS /asboolP hsub]; split.
- move=> [hS hsub]; apply/andP; split=> //; exact/asboolP.
Qed.
