(** Supporting measure bound for the interval-to-set passage in Federer
    (1969), 2.9.22, p. 168. A measure with null singletons bounds an
    arbitrary real set by a uniform bound for the segments joining its
    points. This expands the printed passage from the interval
    derivative-integral estimate to inverse images; it is not claimed as a
    separately numbered book theorem. Only general real topology,
    separability and the project's measure continuity are used. Chapter 21
    omits 2.9.22. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealLineSeparability MetricSubsetBackground
  MetricSubsetSeparability SeparableClosedCover SeparablePointSequenceUP SeparablePointSequenceSealed
  RealSequenceIntervalHull MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic MeasureContinuityBelow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [atomless_real_interval_hull_bound]: supporting
    exhaustion for Federer 2.9.22, p. 168, after the interval
    integral bound. A countable dense sequence in A supplies nested
    finite hulls whose endpoints belong to A. They cover every point
    except a possible minimum and maximum; null singletons remove
    these two exceptions. The set A need not be measurable or bounded. *)
Theorem atomless_real_interval_hull_bound (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (hm : is_measure mu)
    (A : set (real_line_metric R)) (M : \bar R) :
  (forall x, mu [set x]=0%E) ->
  (forall a b : R, measure_measurable mu `[a,b]) -> (0<=M)%E ->
  (forall a b : R, A a -> A b -> a<=b -> (mu `[a,b]<=M)%E) ->
  (mu A<=M)%E.
Proof.
move=> hz hmeas hM hbound.
case: (pselect (A !=set0))=> [[a0 ha0]|hEmpty]; last first.
  have hA : A=set0 by apply/seteqP; split=> x // hx; exfalso; apply: hEmpty; exists x.
  by rewrite hA (measure_empty hm).
have [D [hDc hDd]] := @metric_subset_separable R [the metricType R of real_line_metric R]
  A (real_line_countable_dense R).
pose z0 : metric_subset A := @exist (real_line_metric R) (fun x => x \in A) a0 (mem_set ha0).
pose q := @SeparablePointSequence.value R [the metricType R of metric_subset A] z0 D hDc hDd.
have hq := @SeparablePointSequence.laws R [the metricType R of metric_subset A] z0 D hDc hDd.
pose p n : R := val (q n).
have hp n : A (p n) := set_valP (q n).
pose I n : set (real_line_metric R) := `[real_prefix_low p n,real_prefix_high p n].
have hI n : measure_measurable mu (I n) := hmeas _ _.
have hIn n m : (n<=m)%N -> I n `<=` I m.
  move=> hnm x; rewrite /I /= !in_itv /= => /andP [hl hu].
  apply/andP; split.
  - exact: le_trans (real_prefix_low_antitone p hnm) hl.
  - exact: le_trans hu (real_prefix_high_monotone p hnm).
have hIB n : (mu (I n)<=M)%E.
  have [i [_ hi]] := real_prefix_low_member p n.
  have [j [_ hj]] := real_prefix_high_member p n.
  apply: hbound; [by rewrite hi|by rewrite hj|].
  exact: le_trans (real_prefix_low_bound p (leqnn n)) (real_prefix_high_bound p (leqnn n)).
have hU : (mu (\bigcup_n I n)<=M)%E.
  have [_ [hl _]] := @measure_continuity_below R (real_line_metric R) mu hm I hI hIn.
  rewrite leNgt; apply/negP=> hlt.
  have [n hn] := hl M hlt.
  by have := hn n (leqnn n); rewrite ltNge hIB.
pose B := [set x : real_line_metric R | A x /\ forall y, A y -> x<=y].
pose C := [set x : real_line_metric R | A x /\ forall y, A y -> y<=x].
have hB : mu B=0%E.
  case: (pselect (B !=set0))=> [[b [hb hmin]]|hempty].
  - apply: (@measure_null_subset R (real_line_metric R) mu hm B [set b]) (hz b).
    move=> x [hx hxmin]; apply: le_anti; by rewrite (hxmin b hb) (hmin x hx).
  - have he : B=set0 by apply/seteqP; split=> x // hx; exfalso; apply: hempty; exists x.
    by rewrite he (measure_empty hm).
have hC : mu C=0%E.
  case: (pselect (C !=set0))=> [[c [hc hmax]]|hempty].
  - apply: (@measure_null_subset R (real_line_metric R) mu hm C [set c]) (hz c).
    move=> x [hx hxmax]; apply: le_anti; by rewrite (hmax x hx) (hxmax c hc).
  - have he : C=set0 by apply/seteqP; split=> x // hx; exfalso; apply: hempty; exists x.
    by rewrite he (measure_empty hm).
have hcover : A `<=` (B `|` C) `|` (\bigcup_n I n).
  move=> x hx.
  case: (pselect (exists u, A u /\ u<x))=> [[u [hu hux]]|hmin]; last first.
    left; left; split=> // y hy; rewrite leNgt; apply/negP=> hyx; apply: hmin; by exists y.
  case: (pselect (exists v, A v /\ x<v))=> [[v [hv hxv]]|hmax]; last first.
    left; right; split=> // y hy; rewrite leNgt; apply/negP=> hxy; apply: hmax; by exists y.
  pose zu : metric_subset A := @exist (real_line_metric R) (fun t => t \in A) u (mem_set hu).
  pose zv : metric_subset A := @exist (real_line_metric R) (fun t => t \in A) v (mem_set hv).
  have heu : 0<x-u by rewrite subr_gt0.
  have hev : 0<v-x by rewrite subr_gt0.
  have [r [[i _ hir] hnear]] := metric_dense_point_near hq.2 zu heu.
  have [s [[j _ hjs] hfar]] := metric_dense_point_near hq.2 zv hev.
  have hip : p i<x.
    change (is_true (`|u-val r|<x-u)) in hnear.
    have hn : `|val r-u|<x-u by rewrite distrC.
    have hb := le_lt_trans (ler_norm (val r-u)) hn.
    rewrite /p /q hir; lra.
  have hjp : x<p j.
    change (is_true (`|v-val s|<v-x)) in hfar.
    have hb := le_lt_trans (ler_norm (v-val s)) hfar.
    rewrite /p /q hjs; lra.
  right; exists (maxn i j); first exact Logic.I.
  rewrite /I /= in_itv /=; apply/andP; split.
  - exact: le_trans (real_prefix_low_bound p (leq_maxl i j)) (ltW hip).
  - exact: le_trans (ltW hjp) (real_prefix_high_bound p (leq_maxr i j)).
have hb := @measure_binary_cover R (real_line_metric R) mu hm A (B `|` C) (\bigcup_n I n) hcover.
rewrite (@measure_null_union R (real_line_metric R) mu hm B C hB hC) add0e in hb.
exact: le_trans hb hU.
Qed.
