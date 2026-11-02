(** Federer (1969), 2.10.28, p. 191: the real power-gauge measure agrees
    with compact interval covers. For the remaining inequality replace every
    eligible finite-diameter unrestricted generator by a same-diameter
    compact interval. Work only at finite cutoffs, keeping repeated hulls
    indexed so their cost sum is controlled. The coefficient remains
    explicit, before Euler-Gamma normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower MetricDiameter CompactIntervalGauge
  ConcaveIntervalMeasure MetricRealPowerCost MetricRealPowerMeasureUP MetricRealPowerMeasure
  MetricRealPowerIntervalHull HausdorffLengthUP CaratheodoryLimitUP CaratheodoryBorelRegular
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [interval_measure_below_metric_real_power]: supporting
    interval-cover inequality in the real-line
    power-measure assertion of 2.10.28, p. 191.
    No boundedness or measurability premise is
    imposed on the target A. Only generators
    eligible at a chosen finite cutoff are
    replaced by compact interval hulls. *)
Theorem interval_measure_below_metric_real_power (R : realType) (c p : R) :
  (0<=c)%R -> (0<=p)%R -> forall A : set (real_line_metric R),
  concave_interval_measure (fun x=>(c*real_power x p)%R) A<=
    @metric_real_power_measure R [the metricType R of real_line_metric R] c p A.
Proof.
move=> hc hp A.
pose X := [the metricType R of real_line_metric R].
pose I := compact_real_intervals R.
pose J := @nonempty_metric_sets R X.
pose h := fun x : R=>(c*real_power x p)%R.
pose cost := fun S : J=>metric_real_diameter_cost c p (val S).
pose icost := fun T : I=>(concave_interval_cost h (val T))%:E.
pose mu := @metric_real_power_measure R X c p.
have hmu := @metric_real_power_measure_specification R X c p.
apply: (caratheodory_limit_least (@concave_interval_measure_specification R h))=> delta xi hd hxi.
have [n hcut] := @reciprocal_metric_cutoffs_cofinal R delta hd.
pose e := ((n.+1%:R : R)^-1)%R.
have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
pose nu := metric_scale_envelope (fun S : J=>val S) cost e%:E.
have hnu := @metric_scale_envelope_specification R X J (fun S=>val S) cost e%:E.
have heE : 0<e%:E by rewrite lte_fin.
have hnuUpper : nu A<=mu A := @caratheodory_limit_upper R X J (fun S=>val S) cost mu hmu A e%:E nu heE hnu.
have hbound : xi A<=nu A.
  apply: (metric_scale_envelope_greatest hnu)=> G hG hsize hcover.
  pose eligible (S : J) := extended_metric_diameter (val S)<=e%:E.
  have hpoint : is_compact_real_interval (`[0%R,0%R] : set (real_line_metric R)).
    exists 0%R,0%R; by split.
  pose T0 : I := Sub (`[0%R,0%R] : set (real_line_metric R)) (mem_set hpoint).
  have hex (S : J) : exists T : I, eligible S ->
      val S `<=` val T /\ extended_metric_diameter (val T)=extended_metric_diameter (val S) /\ icost T=cost S.
    case: (pselect (eligible S))=> hS.
    - have hfinite : extended_metric_diameter (val S)< +oo := le_lt_trans hS (ltry e).
      have [T [hST [hdiam hcost]]] := @real_power_cover_interval_exists R c p (val S) (set_valP S) hfinite.
      exists T=> _; split=> //; by split.
    - exists T0=> hfalse; exact: False_rect _ (hS hfalse).
  pose q (S : J) := projT1 (cid (hex S)).
  have hq S (hS : eligible S) := projT2 (cid (hex S)) hS.
  have hqnonnegative S : G S -> 0<=icost (q S).
    move=> hS; rewrite (hq S (hsize S hS)).2.2.
    exact (@metric_real_power_cost_nonnegative R c p _ hc).
  have hqdiam S : G S -> extended_metric_diameter (val (q S))<=delta.
    move=> hS; rewrite (hq S (hsize S hS)).2.1.
    exact: le_trans (hsize S hS) hcut.
  have hqcover : A `<=` \bigcup_(S in G) val (q S).
    move=> x hx; have [S hS hxS] := hcover x hx.
    exists S=> //; exact: (hq S (hsize S hS)).1 x hxS.
  have hh := @metric_scale_envelope_indexed_cover R X I J (fun T=>val T) icost delta xi hxi
    A G q hG hqnonnegative hqdiam hqcover.
  have hsum : nonnegative_sum G (fun S=>icost (q S))=nonnegative_sum G cost.
    apply: nonnegative_sum_ext=> S hS; exact: (hq S (hsize S hS)).2.2.
  by rewrite hsum in hh.
exact: le_trans hbound hnuUpper.
Qed.
