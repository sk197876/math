(** Federer (1969), 2.10.14, p. 177: the lower variation estimate follows by
    summing endpoint estimates over a partition. Open image-measure
    intervals and the two opposite half-open atomic intervals are disjoint
    at subdivision points. This supplies the proof omitted in the book,
    using 2.5.16, p. 109, and 2.10.10, p. 176. the bridge estimate is local
    infrastructure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import IntervalBumpFunctions RealMetricBackground ExtendedRealBounds CurveVariationUP
  CurveJumpBudget CurveJumpEndpointBound CurveImageMeasureLower
  HausdorffLength BorelImageCoverCost BorelCaratheodoryMeasure BorelRegularMeasureUP
  TopologicalBorel StieltjesContinuityPoints StieltjesContinuousIntegrator
  MeasureUP MeasureBasic MeasureFiniteAdditivity MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [half_open_interval_superadditive]: supporting
    disjoint jump-budget addition in 2.10.14, p. 177,
    from measurable additivity in 2.1.2, pp. 53–54. *)
Lemma half_open_interval_superadditive (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (right : bool) (a b c : R) :
  is_measure mu ->
  (forall A, measure_measurable mu A) -> (a<=b)%R -> (b<=c)%R ->
  mu (if right then `[a,b[ else `]a,b])+
    mu (if right then `[b,c[ else `]b,c])<=
    mu (if right then `[a,c[ else `]a,c]).
Proof.
move=> hm hmeas hab hbc.
case: right.
- rewrite -(measure_disjoint_union (hmeas `[a,b[) (_ : forall x, `[a,b[ x -> `[b,c[ x -> False)).
  2: by move=> x; rewrite /= !in_itv /= => /andP[_ hxb] /andP[hbx _]; move: (lt_le_trans hxb hbx); rewrite ltxx.
  apply: (measure_mono hm)=> x.
  rewrite /= !in_itv /= => -[/andP[ha hb]|/andP[hb hc]]; apply/andP; split=> //.
  + exact: lt_le_trans hb hbc.
  + exact: le_trans hab hb.
- rewrite -(measure_disjoint_union (hmeas `]a,b]) (_ : forall x, `]a,b] x -> `]b,c] x -> False)).
  2: by move=> x; rewrite /= !in_itv /= => /andP[_ hxb] /andP[hbx _]; move: (lt_le_trans hbx hxb); rewrite ltxx.
  apply: (measure_mono hm)=> x.
  rewrite /= !in_itv /= => -[/andP[ha hb]|/andP[hb hc]]; apply/andP; split=> //.
  + exact: le_trans hb hbc.
  + exact: le_lt_trans hab hb.
Qed.

(** Source for [metric_chain_sum_interval_cost_bound]: supporting
    partition argument in 2.10.14, p. 177. Any nonnegative
    interval cost dominating increments and superadditive under
    ordered concatenation dominates the entire chain. *)
Lemma metric_chain_sum_interval_cost_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (C : R -> R -> \bar R) (s : seq R) :
  (forall a b, 0<=C a b) ->
  (forall a b, (a<=b)%R -> (mdist (g a) (g b))%:E<=C a b) ->
  (forall a b c, (a<=b)%R -> (b<=c)%R -> C a b+C b c<=C a c) ->
  sorted <=%O s -> (chain_sum g s)%:E<=C (head 0%R s) (last 0%R s).
Proof.
move=> hnon hinc hcat; elim: s=> [|t [|u rest] ih] hs.
- exact: hnon.
- exact: hnon.
have /andP[htu hs'] := hs.
have hul : (u<=last u rest)%R.
  by have := @sorted_le_last R (u :: rest) 0%R u hs' (mem_head u rest); rewrite /=.
have hih := ih hs'; rewrite [head _ _]/= [last _ _]/= in hih.
rewrite chain_sum_cons EFinD [head _ _]/= [last _ _]/=.
exact: le_trans (leeD (hinc t u htu) hih) (hcat t u _ htu hul).
Qed.

(** Source for [finite_jump_curve_variation_image_measure_lower]:
    supporting lower estimate in 2.10.14, p. 177, for a
    globally finite jump budget. No variation or continuity hypothesis
    is imposed on the curve. The source-retracted representative
    supplies this global hypothesis in the final theorem. *)
Theorem finite_jump_curve_variation_image_measure_lower (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) :
  curve_jump_measure g true setT+curve_jump_measure g false setT< +oo ->
  curve_variation g a b<=
    @borel_caratheodory_measure R [the metricType R of real_line_metric R]
      (borel_image_cover_cost g (@hausdorff_length R Y)) `]a,b[+
    curve_interval_jump_budget g a b.
Proof.
move=> hfin.
pose phi := @borel_caratheodory_measure R [the metricType R of real_line_metric R]
  (borel_image_cover_cost g (@hausdorff_length R Y)).
have hcost := @borel_image_cover_cost_laws R [the topologicalType of real_line_metric R]
  Y g (@hausdorff_length R Y) (@hausdorff_length_is_measure R Y).
have hm := borel_caratheodory_is_measure hcost.
have hr := borel_caratheodory_borel_regular hcost.
pose C u v := phi `]u,v[+curve_interval_jump_budget g u v.
have hnon u v : 0<=C u v.
  apply: adde_ge0; first exact: measure_nonnegative hm _.
  exact: curve_interval_jump_budget_nonnegative.
have hinc u v : (u<=v)%R -> (mdist (g u) (g v))%:E<=C u v.
  rewrite le_eqVlt=> /orP[/eqP <-|huv].
    rewrite mdistxx; exact: hnon.
  have hJ : curve_interval_jump_budget g u v< +oo.
    apply: le_lt_trans _ hfin; apply: leeD;
      apply: (measure_mono (curve_jump_measure_is_measure g _))=> x hx; exact I.
  have hh := curve_endpoint_jump_budget_bound huv hJ.
  have hb := @borel_caratheodory_cost_bound R [the metricType R of real_line_metric R]
    _ hcost `[u,v] (closed_borel_set (@segment_closed_real R u v)).
  have he := @measure_segment_open_interval R phi u v hm
    (@curve_image_measure_singleton_null R Y g u) (@curve_image_measure_singleton_null R Y g v).
  rewrite /phi in he; rewrite he in hb.
  exact: le_trans hh (leeD hb (lexx _)).
have hcat u v w : (u<=v)%R -> (v<=w)%R -> C u v+C v w<=C u w.
  move=> huv hvw; rewrite /C /curve_interval_jump_budget.
  rewrite (addeA (phi `]u,v[)) (addeA (phi `]v,w[)) (addeA (phi `]u,w[)).
  rewrite (addeACA (phi `]u,v[+curve_jump_measure g true `[u,v[)
    (curve_jump_measure g false `]u,v]) (phi `]v,w[+curve_jump_measure g true `[v,w[)
    (curve_jump_measure g false `]v,w])).
  rewrite (addeACA (phi `]u,v[) (curve_jump_measure g true `[u,v[)
    (phi `]v,w[) (curve_jump_measure g true `[v,w[)).
  apply: leeD; last first.
    exact: (@half_open_interval_superadditive R _ false u v w
      (curve_jump_measure_is_measure g false) (curve_jump_measure_all_sets_measurable g false) huv hvw).
  apply: leeD.
  - have hmeas : measure_measurable phi `]u,v[.
      apply: (borel_regular_borel_measurable hm hr); apply: open_borel_set; exact: interval_open.
    exact: (@open_interval_superadditive R phi u v w hm hmeas huv hvw).
  - exact: (@half_open_interval_superadditive R _ true u v w
      (curve_jump_measure_is_measure g true) (curve_jump_measure_all_sets_measurable g true) huv hvw).
apply: extended_real_sup_least=> z [s [[hs [hn [hh hl]]] ->]].
have hh0 : head 0%R s=a by case: s hn hh hl hs=> //.
have hl0 : last 0%R s=b by case: s hn hh hl hs {hh0}=> //.
have hb := metric_chain_sum_interval_cost_bound hnon hinc hcat hs.
by rewrite hh0 hl0 in hb.
Qed.
