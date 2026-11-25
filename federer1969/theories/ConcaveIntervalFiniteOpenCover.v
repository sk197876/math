(** Federer (1969), 2.10.28(3), p. 192: supporting finite open cover of a
    compact set at any strict budget above its interval-generated measure.
    Allocate summable errors to a near-optimal countable closed cover,
    enlarge its intervals, and take a finite open subcover. Keep source
    indices if open enlargements coincide; no injectivity is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws
  ConcaveIntervalMeasure ConcaveIntervalOpenEnlargement StieltjesCaratheodoryUP CaratheodoryLimitUP
  MetricScaleEnvelope MetricScaleApproximation NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd
  CountableGeometricBudget CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [concave_interval_compact_finite_open_cover_below]:
    supporting finite-cover reduction in the lower-bound proof of
    2.10.28(3), p. 192 Cover intervals are indexed by finitely many original
    generators, so repetitions cost repeatedly and require no injectivity
    premise. The compact set may be empty. *)
Theorem concave_interval_compact_finite_open_cover_below (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (C : set (real_line_metric R)) (q : R) :
  compact C -> concave_interval_measure h C<q%:E ->
  exists (F : {fset compact_real_intervals R})
    (U : compact_real_intervals R -> stieltjes_open_intervals R),
    C `<=` \bigcup_(S in [set` F]) stieltjes_interval_set (U S) /\
    (\sum_(S <- F) h ((val (U S)).2-(val (U S)).1)<q)%R.
Proof.
move=> hC hbudget.
pose I := compact_real_intervals R.
pose S := fun j : I=>val j.
pose c := fun j : I=>(concave_interval_cost h (val j))%:E.
pose nu := @metric_scale_envelope R [the metricType R of real_line_metric R] I S c 1%E.
have hn := @metric_scale_envelope_specification R [the metricType R of real_line_metric R] I S c 1%E.
have hpos : (0<(1 : \bar R)) by rewrite lte_fin ltr01.
have hbelow := @caratheodory_limit_upper R [the metricType R of real_line_metric R] I S c _
  (concave_interval_measure_specification h) C 1%E nu hpos hn.
have [G [hG [hdiam [hcover hcost]]]] := metric_scale_envelope_approximation hn (le_lt_trans hbelow hbudget).
have hcost0 : 0<=nonnegative_sum G c := nonnegative_sum_nonnegative G c.
have hfinite : nonnegative_sum G c \is a fin_num.
  rewrite (ge0_fin_numE hcost0); exact: lt_trans hcost (ltry q).
pose M := fine (nonnegative_sum G c).
have hM : nonnegative_sum G c=M%:E by rewrite /M fineK.
have hMq : (M<q)%R by move: hcost; rewrite hM lte_fin.
pose e := (q-M)%R.
have he : (0<e)%R by rewrite /e subr_gt0.
have [b [hb hbsum]] := @countable_geometric_error_budget R I G e hG he.
have hex (j : I) := @concave_interval_open_enlargement_exists R h hg j (b j) (hb j).
pose U (j : I) := projT1 (cid (hex j)).
have hU (j : I) := projT2 (cid (hex j)).
pose a (j : I) := h (((val (U j)).2-(val (U j)).1)%R).
have ha (j : I) : (0<=a j)%R.
  apply: (@concave_interval_gauge_nonnegative R h hg _).
  have hh : ((val (U j)).1<(val (U j)).2)%R := set_valP (U j).
  by rewrite subr_ge0; exact: ltW hh.
have hc (j : I) : 0<=c j by rewrite /c lee_fin; exact: (@concave_interval_cost_nonnegative R h hg (val j)).
have hsum : nonnegative_sum G (fun j=>(a j)%:E)<=nonnegative_sum G c+nonnegative_sum G (fun j=>(b j)%:E).
  rewrite -(@nonnegative_sum_add R I G c (fun j=>(b j)%:E) (fun j _=>hc j)
    (fun j _=>ltW (hb j))).
  apply: nonnegative_sum_mono=> j hj.
  rewrite /c -EFinD lee_fin; exact: ltW (hU j).2.
have hsumq : nonnegative_sum G (fun j=>(a j)%:E)<q%:E.
  apply: le_lt_trans (le_trans hsum (leeD (lexx _) hbsum)) _.
  rewrite hM -EFinD lte_fin /e; lra.
have hcoverU : C `<=` \bigcup_(j in G) stieltjes_interval_set (U j).
  move=> x hx; have [j hj hxj] := hcover x hx; exists j=> //; exact: (hU j).1 x hxj.
have hopen (j : I) : open (stieltjes_interval_set (U j)) by exact: interval_open.
have [F hFG hFC] := @compact_open_finite_cover (real_line_metric R) I G
  (fun j=>stieltjes_interval_set (U j)) C hC (fun j _=>hopen j) hcoverU.
have hFsub : [set j : I | j \in F] `<=` G by move=> j hj; exact: set_mem (hFG j hj).
have hfinitebound := @nonnegative_sum_subset R I [set j : I | j \in F] G (fun j=>(a j)%:E) hFsub.
rewrite (@nonnegative_sum_finite R I F (fun j=>(a j)%:E)
  (fun j _=>ha j)) sumEFin in hfinitebound.
have hlast := le_lt_trans hfinitebound hsumq.
rewrite lte_fin in hlast.
exists F,U; split=> //; exact hlast.
Qed.
