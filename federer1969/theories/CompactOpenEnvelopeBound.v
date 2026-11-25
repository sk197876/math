(** Open neighbourhood proof for the compact assertions in Federer (1969),
    2.10.20, p. 182. The infimum of masses of open supersets is used only
    through the proved sealed interface of 2.5.14, pp. 107–108. it does not
    state this fixed-cutoff compact-sequence result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic OpenCoverContentUP OpenCoverEnvelope
  MetricScaleEnvelopeUP MetricScaleCutoffCost ExtendedRealBounds CompactDecreasingNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_open_cover_content]: supporting
    open-envelope existence for 2.10.20, p. 182.
    Any measure supplies the open-content laws of
    2.5.14, pp. 107–108; no topological regularity
    or finiteness assumption is added. *)
Lemma measure_open_cover_content (R : realType) (X : topologicalType)
    (nu : set X -> \bar R) : is_measure nu -> is_open_cover_content nu.
Proof.
move=> hm; constructor.
- move=> V _; exact: (@measure_nonnegative R X nu hm V).
- exact: measure_empty hm.
- move=> W C hW hC hOpen hcov; exact: (@measure_countable_cover R X nu hm W C hC hcov).
Qed.

(** Source for [compact_decreasing_open_envelope_bound]: supporting
    neighbourhood estimate for both compact-sequence claims
    in 2.10.20, p. 182. The infimum of nu(C_n)
    is bounded by the open envelope of their intersection.
    Closed decreasing subsets of compact C_0 suffice. *)
Lemma compact_decreasing_open_envelope_bound (R : realType) (X : topologicalType)
    (nu omega : set X -> \bar R) (C : nat -> set X) :
  is_measure nu -> is_open_cover_envelope nu omega ->
  compact (C 0%N) -> (forall n, closed (C n)) ->
  (forall n m, (n<=m)%N -> C m `<=` C n) ->
  extended_real_inf [set b | exists n, b=nu (C n)]<=omega (\bigcap_n C n).
Proof.
move=> hm ho hC0 hclosed hdec.
apply: (open_cover_envelope_greatest ho)=> V hV hKV.
have [N hN] := compact_decreasing_eventually_in_open hC0 hclosed hdec hV hKV.
have hv : [set b | exists n, b=nu (C n)] (nu (C N)) by exists N.
apply: le_trans (extended_real_inf_lower hv) _.
exact: (@measure_mono R X nu hm (C N) V (hN N (leqnn N))).
Qed.

(** Source for [metric_scale_open_generator_envelope]: supporting
    open-generator case of 2.10.20, p. 182.
    A countable cover by open generators has an open
    union whose scale mass is bounded by the same
    cost. Hence the scale equals its open envelope,
    without requiring finite mass or a positive cutoff. *)
Lemma metric_scale_open_generator_envelope (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R) (delta : \bar R)
    (nu : set X -> \bar R) :
  is_metric_scale_envelope S c delta nu -> (forall j, 0<=c j) ->
  (forall j, open (S j)) -> is_open_cover_envelope nu nu.
Proof.
move=> hn hc hOpen; have hm := metric_scale_envelope_is_measure hn hc.
constructor.
- move=> A V hV hAV; exact: (@measure_mono R X nu hm A V hAV).
- move=> A b hb; apply: (metric_scale_envelope_greatest hn)=> G hG hdiam hcov.
  pose V := \bigcup_(j in G) S j.
  have hV : open V by apply: bigcup_open=> j hj; exact: hOpen.
  have hlow := hb V hV hcov.
  have hcost := @metric_scale_envelope_lower R X J S c delta nu hn V G hG hdiam
    (fun x hx => hx).
  exact: le_trans hlow hcost.
Qed.
