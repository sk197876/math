(** Federer (1969), 4.1.7, p. 358: Radon
    regularity of the norm-density measure on an
    arbitrary open U. The supporting argument uses
    2.2.2–2.2.3, pp. 61–62, on a countable
    finite open cover, and the compact exhaustion
    from 4.1.1, p. 344. Whole-space finiteness
    and bounded-set finiteness are not added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  RadonMeasureUP RepresentingMeasureComparison CountableCompactOpenInner
  ExtendedScaledErrorBound ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_finite_open_cover_outer_infimum]:
    outer regularity for all target sets, supporting
    Federer 4.1.7, p. 358, by the countable
    finite-open-cover assertion of 2.2.2–2.2.3,
    pp. 61–62. Infinite target masses are retained. *)
Lemma countable_finite_open_cover_outer_infimum (R:realType) (X:metricType R)
    (mu:set X->\bar R) (W:nat->set X):
  is_measure mu ->is_borel_regular_measure mu ->
  (forall n,open (W n) /\ mu (W n)< +oo) ->
  setT `<=` \bigcup_n W n ->forall A c,
  (forall V,open V ->A `<=` V ->c<=mu V) ->c<=mu A.
Proof.
move=>hm hr hW hCover A c hBound.
case:(ltP (mu A) +oo)=>hFinite; last exact:le_trans (leey c) hFinite.
have hNum:mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
pose a:=fine (mu A).
have hAvalue:mu A=a%:E by rewrite /a fineK.
rewrite hAvalue.
apply:(@extended_upper_bound_from_scaled_errors R c a 1%R (@ler01 R))=>e he.
have hOpen n:open (W n):=(hW n).1.
have hAny x:exists n,W n x.
  have [n _ hn]:=hCover x Logic.I; by exists n.
have hFiniteW n:mu (W n)< +oo:=(hW n).2.
have [V [hV [hAV hError]]]:=@borel_regular_open_outer R X W hOpen hAny
  mu hm hr hFiniteW A e he hFinite.
have hEnd:=le_trans (hBound V hV hAV) hError.
rewrite hAvalue -EFinD in hEnd; by rewrite mul1r.
Qed.

(** Source for [countable_locally_finite_metric_radon]:
    the Radon laws of 2.2.5, pp. 62–63,
    for the norm-density measure in Federer 4.1.7,
    p. 358. Both covers are actual subsets of
    the original domain. Compact finiteness, a compact
    cover and a finite open cover are sufficient;
    no properness of the ambient metric is needed. *)
Theorem countable_locally_finite_metric_radon (R:realType) (X:metricType R)
    (mu:set X->\bar R) (C W:nat->set X):
  is_measure mu ->is_borel_regular_measure mu ->locally_compact (@setT X) ->
  (forall K,compact K ->mu K< +oo) ->
  (forall n,compact (C n)) ->setT `<=` \bigcup_n C n ->
  (forall n,open (W n) /\ mu (W n)< +oo) ->setT `<=` \bigcup_n W n ->
  is_radon_measure mu.
Proof.
move=>hm hr hLocal hFinite hC hCover hW hWCover.
constructor.
- exact:metric_hausdorff.
- exact:hLocal.
- exact:hFinite.
- exact:borel_regular_open_measurable hr.
- move=>V hV c hBound.
  rewrite leNgt; apply/negP=>hLower.
  have [q [hQ1 hQ2]]:=extended_rationals_order_dense hLower.
  have hClosed F:closed F ->measure_measurable mu F.
    move=>hF; exact:(borel_regular_borel_measurable hm hr (closed_borel_set hF)).
  have [K [hK [hKV hMass]]]:=
    @countable_compact_open_inner_strict R X mu C V (ratr q)
      hm hC hCover hClosed hV hQ2.
  by have:=lt_le_trans (lt_trans hQ1 hMass) (hBound K hK hKV); rewrite ltxx.
- exact:(@countable_finite_open_cover_outer_infimum R X mu W hm hr hW hWCover).
Qed.
