(** Federer (1969), 2.2.4, p. 62: background for the continuum cardinality
    of an uncountable complete separable metric space. The complement has no
    isolated points: an isolating ball would itself be a countable open
    neighborhood. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import CountableOpenBaseUP CountableNeighborhoodLocus
  MetricClosedBalls MetricSubsetBackground NoIsolatedPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_set_adjoin_point]: Supporting Federer 2.2.4, p.
    62.Adding one point to a countable set preserves countability; this
    bounds an isolating neighborhood. *)
Lemma countable_set_adjoin_point (T : choiceType) (A : set T) (x : T) :
  countable A -> countable (A `|` [set x]).
Proof.
move=> hc; pose F b := if b then A else [set x].
have he : A `|` [set x] = \bigcup_b F b.
  apply/seteqP; split.
  - move=> y [hy|hy]; [exists true|exists false]=> //; exact Logic.I.
  - by move=> y [[] _ hy]; [left|right].
rewrite he; apply: bigcup_countable; first exact: countableP.
move=> [] _ //; exact: countable1.
Qed.

(** Source for [condensation_kernel_no_isolated_points]: Supporting Federer
    2.2.4, p. 62.The metric subspace complementary to all countable
    neighborhoods has no open singleton. *)
Theorem condensation_kernel_no_isolated_points (R : realType) (T : metricType R)
    (U : nat -> set T) : is_countable_open_base U ->
  has_no_isolated_points [the topologicalType of
    metric_subset (~` @countable_neighborhood_locus T)].
Proof.
move=> hU x ho.
pose K := ~` @countable_neighborhood_locus T.
have hn : nbhs x [set x] by rewrite openE in ho; exact: ho x (erefl _).
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x [set x]) hn.
pose B := [set y : T | mdist (val x) y < e].
have hsub : B `<=` countable_neighborhood_locus `|` [set val x].
  move=> y hy; case: (pselect (countable_neighborhood_locus y))=> hu; first by left.
  right; have hyK : K y := hu.
  pose z : metric_subset K := @exist T (fun t => t \in K) y (mem_set hyK).
  have hzx : z = x := hb z hy.
  exact (congr1 (fun a : metric_subset K => (val a : T)) hzx).
have hc : countable B.
  apply: sub_countable (subset_card_le hsub) _.
  apply: countable_set_adjoin_point; exact: countable_neighborhood_locus_countable hU.
have hxK : ~ countable_neighborhood_locus (val x) := set_valP x.
apply: hxK; exists B; split; first exact: metric_open_ball_open.
split=> //; by rewrite /B /= mdistxx.
Qed.
