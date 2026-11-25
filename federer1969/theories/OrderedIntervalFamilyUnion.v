(** Federer (1969), 2.9.20, p. 166: finite unions of ordered nondegenerate
    intervals in the proofs of (2)=>(3) and (3)=>(4). We use their open
    interiors; a later atomless-measure law restores closed endpoints when
    needed. Source context: OrderedIntervalFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground OrderedIntervalFamilyUP MeasureUP
  MeasureBasic MeasureSplit MeasureFiniteClosure MeasureFiniteAdditivity LebesgueScalarMeasure
  StieltjesContinuityPoints TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_interval_family_open_union]: direct finite union used
    in Federer 2.9.20, p. 166 The endpoints are omitted so adjacent cells
    are disjoint even when they share a boundary point. *)
Definition real_interval_family_open_union (R : realType) (s : seq (R * R)) : set R :=
  [set x | exists uv, uv \in s /\ `]uv.1,uv.2[ x].

(** Source for [real_interval_family_open_union_empty]: supporting
    empty-family boundary case in Federer 2.9.20(3), p. 165. *)
Lemma real_interval_family_open_union_empty (R : realType) :
  @real_interval_family_open_union R [::]=set0.
Proof. by apply/seteqP; split=> x // [uv []]. Qed.

(** Source for [real_interval_family_open_union_cons]: supporting
    finite-union induction in Federer 2.9.20, p. 166. *)
Lemma real_interval_family_open_union_cons (R : realType) (u v : R)
    (s : seq (R * R)) : real_interval_family_open_union ((u,v)::s)=
  `]u,v[ `|` real_interval_family_open_union s.
Proof.
apply/seteqP; split=> x.
- move=> [uv [huv hx]]; move: huv; rewrite inE=> /orP[/eqP heq|huv].
    left; by move: hx; rewrite heq.
  right; by exists uv.
- move=> [hx|[uv [huv hx]]].
  + exists (u,v); split=> //; by rewrite inE eqxx.
  + exists uv; split=> //; by rewrite inE huv orbT.
Qed.

(** Source for [real_interval_family_open_union_subset]: supporting ambient
    segment inclusion in Federer 2.9.20, p. 166 *)
Lemma real_interval_family_open_union_subset (R : realType) (a b : R)
    (s : seq (R * R)) : is_ordered_real_interval_family a b s ->
  real_interval_family_open_union s `<=` `[a,b].
Proof.
move=> hs x [[u v] [huv hx]].
have [hau [_ hvb]] := ordered_real_interval_family_cell_bounds hs huv.
move: hx; rewrite /= !in_itv /= => /andP[hux hxv].
by rewrite (le_trans hau (ltW hux)) (le_trans (ltW hxv) hvb).
Qed.

(** Source for [real_interval_family_open_union_measurable]: supporting
    measurable finite-union assertion in Federer 2.9.20, p. 166 *)
Lemma real_interval_family_open_union_measurable (R : realType)
    (mu : set R -> \bar R) (s : seq (R * R)) : is_measure mu ->
  (forall u v : R, measure_measurable mu `]u,v[) ->
  measure_measurable mu (real_interval_family_open_union s).
Proof.
move=> hm hI; elim: s=> [|[u v] s ih].
- rewrite real_interval_family_open_union_empty; exact: measure_measurable_empty hm.
- rewrite real_interval_family_open_union_cons.
  exact (@measure_measurable_union R R mu hm `]u,v[ (real_interval_family_open_union s) (hI u v) ih).
Qed.

(** Source for [real_interval_family_open_union_measure]: supporting finite
    disjoint additivity in Federer 2.9.20, p. 166 The family laws make
    distinct interiors disjoint; no atomlessness hypothesis is needed. *)
Lemma real_interval_family_open_union_measure (R : realType)
    (mu : set R -> \bar R) (a b : R) (s : seq (R * R)) :
  is_measure mu -> (forall u v : R, measure_measurable mu `]u,v[) ->
  is_ordered_real_interval_family a b s ->
  mu (real_interval_family_open_union s)=\sum_(uv <- s) mu `]uv.1,uv.2[.
Proof.
move=> hm hI; elim: s a=> [|[u v] s ih] a hs.
- by rewrite real_interval_family_open_union_empty (measure_empty hm) big_nil.
- have [hau [huv [hvb hs']]] := hs.
  have hdis : forall x, `]u,v[ x -> real_interval_family_open_union s x -> False.
    move=> x hx [[p q] [hpq hx']].
    have [hvp [_ _]] := ordered_real_interval_family_cell_bounds hs' hpq.
    move: hx hx'; rewrite /= !in_itv /= => /andP[_ hxv] /andP[hpx _].
    by have := lt_trans hxv (le_lt_trans hvp hpx); rewrite ltxx.
  by rewrite real_interval_family_open_union_cons (measure_disjoint_union (hI u v) hdis)
    (ih v hs') big_cons.
Qed.

(** Source for [real_interval_family_open_union_length]: supporting length
    computation in Federer 2.9.20, p. 166 The Lebesgue measure of the
    disjoint interiors equals the sum of all cell lengths. *)
Lemma real_interval_family_open_union_length (R : realType) (a b : R)
    (s : seq (R * R)) : is_ordered_real_interval_family a b s ->
  lebesgue_scalar_measure (real_interval_family_open_union s)=
    (real_interval_family_length s)%:E.
Proof.
move=> hs; have hm := lebesgue_scalar_is_measure R.
have hI u v : measure_measurable (@lebesgue_scalar_measure R) `]u,v[.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set; exact: interval_open.
rewrite (@real_interval_family_open_union_measure R _ a b s hm hI hs)
  /real_interval_family_length -sumEFin !big_seq.
apply: eq_bigr=> uv huv; case: uv huv=> u v huv.
have [_ [huv' _]] := ordered_real_interval_family_cell_bounds hs huv.
rewrite -(@measure_segment_open_interval R (@lebesgue_scalar_measure R) u v hm
  (lebesgue_scalar_singleton u) (lebesgue_scalar_singleton v)).
exact: lebesgue_scalar_segment (ltW huv').
Qed.
