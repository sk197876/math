(** Federer (1969), 2.10.28(3), p. 192: the lower mass bound for A inside
    every interval of a tree level. Only positive-cost descendants need a
    point of A; zero-cost dead branches contribute nothing. The proof uses
    the abstract limit laws and no construction implementation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalDiameter
  ConcaveIntervalGaugeUP ConcaveIntervalMeasure ConcaveIntervalFiniteOpenCover CompactIntervalCoverMargin
  SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalDescendants SpecialIntervalTreeTopology
  SpecialIntervalLimitLaws StieltjesCaratheodoryUP MetricDiameter MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_28_3_lower]: direct lower
    half of the equality conclusion in
    2.10.28(3), p. 192, for every
    interval T at every level. Preserve
    zero-cost members and all mesh/finite-family
    hypotheses. No nonempty-limit premise is added. *)
Theorem federer_2_10_28_3_lower (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) (A : set (real_line_metric R))
    (hA : is_special_interval_tree_limit H A) j (T : compact_real_intervals R) :
  T \in H j ->
  ((concave_interval_cost h (val T))%:E<=concave_interval_measure h (A `&` val T))%E.
Proof.
move=> hT.
have hnonT := @concave_interval_cost_nonnegative R h hg (val T).
case: (leP (concave_interval_cost h (val T)) 0)=> [hT0|hTpos].
- have heq : concave_interval_cost h (val T)=0 by apply/eqP; rewrite eq_le hT0 hnonT.
  rewrite heq; exact (@measure_nonnegative R [the choiceType of real_line_metric R]
    (concave_interval_measure h) (@concave_interval_measure_is_measure R h hg) (A `&` val T)).
rewrite leNgt; apply/negP=> hsmall.
pose C := A `&` val T.
have hC : compact C := compact_closedI (interval_tree_limit_compact hA) (compact_real_interval_closed (set_valP T)).
have [F [U [hcover hbudget]]] := @concave_interval_compact_finite_open_cover_below R h hg C
  (concave_interval_cost h (val T)) hC hsmall.
pose I := compact_real_intervals R.
have [e [he hsmallsets]] := @compact_interval_cover_small_sets R I F U C hC hcover.
have [N hmesh] := @special_tree_mesh R h H ht e he.
pose G := special_interval_restriction (H (j+N)%N) (val T).
have hG := @special_interval_descendants_special R h hg H ht j T hT N.
have hWpred (i : I) : is_compact_real_interval (`[(val (U i)).1,(val (U i)).2] : set (real_line_metric R)).
  exists (val (U i)).1,(val (U i)).2; split=> //; exact: ltW (set_valP (U i)).
pose W (i : I) : I := Sub (`[(val (U i)).1,(val (U i)).2] : set (real_line_metric R)) (mem_set (hWpred i)).
pose P (i V : I) := `[< val V `<=` val (W i) >].
have hpositivecover (V : I) (hV : V \in G) (hVpos : 0<concave_interval_cost h (val V)) :
    exists i, i \in F /\ val V `<=` val (W i).
  have [hVlevel hVT] := (special_interval_restriction_membership _ _ _).1 hV.
  have [x [hxA hxV]] := @positive_interval_member_meets_limit R h hg H ht A hA (j+N)%N V hVlevel hVpos.
  have hmeet : C `&` val V !=set0 by exists x; split=> //; split=> //; exact: hVT x hxV.
  have hdiam : (@extended_metric_diameter R [the metricType R of real_line_metric R] (val V)<=e%:E)%E.
    exact ((@compact_interval_diameter_bound R (val V) e (set_valP V)).2
      (hmesh (j+N)%N (leq_addl j N) V hVlevel)).
  have [i [hi hsub]] := hsmallsets (val V) hmeet hdiam.
  exists i; split=> // y hy.
  have hyU := hsub y hy; change (`[(val (U i)).1,(val (U i)).2] y).
  move: hyU; rewrite /stieltjes_interval_set /= !in_itv /= => /andP[hl hr].
  by rewrite (ltW hl) (ltW hr).
have hleafbound (V : I) (hV : V \in G) : concave_interval_cost h (val V)<=
    \sum_(i <- F) (if P i V then concave_interval_cost h (val V) else 0).
  have hnon := @concave_interval_cost_nonnegative R h hg (val V).
  case: (leP (concave_interval_cost h (val V)) 0)=> [hz|hp].
  - have heq : concave_interval_cost h (val V)=0 by apply/eqP; rewrite eq_le hz hnon.
    rewrite heq; apply: sumr_ge0=> i _; case: ifP=> _; exact: lexx.
  - have [i [hi hsub]] := hpositivecover V hV hp.
    have hP : P i V by apply/asboolP.
    rewrite (big_fsetD1 _ hi) /= hP.
    have hrest : 0<=\sum_(k <- (F `\ i)%fset) (if P k V then concave_interval_cost h (val V) else 0).
      apply: sumr_ge0=> k _; case: ifP=> _; [exact hnon | exact: lexx].
    lra.
have hfirst : (\sum_(V <- G) concave_interval_cost h (val V))<=
    \sum_(V <- G) \sum_(i <- F) (if P i V then concave_interval_cost h (val V) else 0).
  rewrite !big_seq; apply: ler_sum=> V hV; exact: hleafbound V hV.
have hswap : (\sum_(V <- G) \sum_(i <- F) (if P i V then concave_interval_cost h (val V) else 0))=
    \sum_(i <- F) \sum_(V <- G | P i V) concave_interval_cost h (val V).
  rewrite exchange_big; apply: eq_big_seq=> i _; by rewrite [RHS]big_mkcond /=.
rewrite hswap in hfirst.
have hinner (i : I) : (\sum_(V <- G | P i V) concave_interval_cost h (val V))<=
    h ((val (U i)).2-(val (U i)).1).
  have hh := @special_interval_envelope R h T G hG (W i).
  have hcost : concave_interval_cost h (val (W i))=h ((val (U i)).2-(val (U i)).1).
    change (concave_interval_cost h (`[(val (U i)).1,(val (U i)).2] : set (real_line_metric R))=
      h ((val (U i)).2-(val (U i)).1)).
    exact: (@concave_interval_cost_segment R h (val (U i)).1 (val (U i)).2 (ltW (set_valP (U i)))).
  by rewrite hcost in hh.
have hlast : (\sum_(i <- F) \sum_(V <- G | P i V) concave_interval_cost h (val V))<=
    \sum_(i <- F) h ((val (U i)).2-(val (U i)).1).
  apply: ler_sum=> i _; exact: hinner.
have hmass := @special_interval_cost_sum R h T G hG.
have hbound : concave_interval_cost h (val T)<=\sum_(i <- F) h ((val (U i)).2-(val (U i)).1).
  rewrite hmass; exact: le_trans hfirst hlast.
by have hf := le_lt_trans hbound hbudget; rewrite ltxx in hf.
Qed.
