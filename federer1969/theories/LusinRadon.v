(** Federer (1969), 2.3.5, pp. 76–77, bracketed Radon case. Source context:
    LusinMetric.v. The same abstract closed-approximation proof is used,
    followed by intersection with a compact inner approximant. This
    equivalent proof organisation avoids duplicating the finite-piece
    construction; it uses exactly the compact approximation of 2.2.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP MeasureBasic
  MeasureSplit MeasurableFunctionUP ClosedApproximationUP TopologicalBorel
  BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity RadonCompactApproximation
  LusinClosedApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_radon]: direct compact conclusion of Federer 2.3.5,
    pp. 76–77 Local compactness and Hausdorff separation are retained in
    is_radon_measure. No finite-total-measure hypothesis is added. *)
Theorem lusin_radon (R : realType) (X : topologicalType) (Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (D : set Y) (A : set X) (f : partial_function X Y) (epsilon : R) :
  countable D -> dense D -> is_measure_measurable_function mu f ->
  measure_measurable mu A -> mu A < +oo -> (0 < epsilon)%R ->
  exists C, compact C /\ C `<=` A /\ mu (A `\` C) < epsilon%:E /\
    partial_function_continuous_on C f.
Proof.
move=> hc hd hf hA hfin he.
have hh : (0 < epsilon / 2)%R by rewrite divr_gt0 // ltr0n.
have hclosed K : closed K -> measure_measurable mu K.
  move=> hK; apply: (@borel_regular_borel_measurable R X mu hm (radon_borel_regular hm hr) K).
  exact: closed_borel_set hK.
have happ H : measure_measurable mu H -> mu H < +oo -> is_closed_approximable mu H.
  move=> hH hfH e hep.
  have [K [hK [hKH herror]]] := @radon_compact_approximation R X mu hm hr H e hH hfH hep.
  exists K; split; first exact: compact_closed (radon_hausdorff hr) hK.
  by split.
have [F [hF [hFA [herror hcont]]]] := @lusin_closed_approximation R X Y mu hm D A f
  (epsilon/2)%R hc hd hclosed happ hf hA hfin hh.
have [K [hK [hKA hKerror]]] := @radon_compact_approximation R X mu hm hr A (epsilon/2)%R hA hfin hh.
exists (K `&` F); split; first exact: compact_closedI hK hF.
split; first by move=> x [hx _]; exact: hKA.
split.
- have hcover : (A `\` (K `&` F)) `<=` (A `\` K) `|` (A `\` F).
    move=> x [ha hn]; case: (pselect (K x))=> hk; last by left; split.
    right; split=> // hf'; apply: hn; by split.
  apply: le_lt_trans (@measure_binary_cover R X mu hm _ _ _ hcover) _.
  have hfinite : mu (A `\` F) \is a fin_num.
    rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm).
    exact: lt_trans herror (ltry _).
  have hb := lte_leD hfinite hKerror (ltW herror).
  by rewrite -EFinD -splitr in hb.
- apply: (@partial_continuity_subset X Y (K `&` F) F f _ hcont).
  by move=> x [_ hx].
Qed.
