(** Federer (1969), 2.10.23, p. 186: compact subsets detect every strict
    finite lower bound on the mass of a Suslin set. First work within a
    compact containing set, then use the final-measure radial exhaustion of
    2.10.20, p. 182. No local finiteness of the final measure is assumed.
    Source context and the pruning estimate:
    CompactCostSuslinApproximation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactGeneratorCostUP CompactCostScaleFinite
  CompactCostSuslinApproximation CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryMetricMeasure
  CaratheodoryScaleConvergence MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost
  MeasureUP MeasureBasic MeasureFiniteClosure MeasurableBallRadialContinuity RadialMassSupremum
  LipschitzFunctionCompact MetricClosedBalls SuslinSetUP BorelSuslinImages BorelClosedProjection TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_suslin_bounded_mass_bound]: supporting
    compact-ambient case of 2.10.23, p. 186.
    Any finite common upper bound for masses of
    compact subsets bounds the Suslin set itself. *)
Theorem compact_cost_suslin_bounded_mass_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (psi : set X -> \bar R) (S K : set X) (b : R) :
  metric_boundedly_compact X ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) psi ->
  compact K -> S `<=` K -> is_suslin_set R S ->
  (forall C, compact C -> C `<=` S -> (psi C<=b%:E)%E) -> (psi S<=b%:E)%E.
Proof.
move=> hX hpsi hK hSK hS hbound; rewrite leNgt; apply/negP=> hbad.
have hlim := caratheodory_limit_positive_cutoff_convergence S hpsi.
have [d [hd hnear]] := hlim.1 b%:E hbad.
pose delta := d/2.
have hdpos : 0<delta by rewrite /delta divr_gt0 // ltr0n.
have hdd : (delta%:E<d%:E)%E by rewrite lte_fin /delta; lra.
have hdelta : (0<delta%:E)%E by rewrite lte_fin.
pose nu := metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) delta%:E.
have hn := @metric_scale_envelope_specification R X (compact_metric_set X) (fun C=>val C) (fun C=>(c C)%:E) delta%:E.
have hlower : (b%:E<nu S)%E := hnear delta%:E hdelta hdd.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := metric_scale_envelope_is_measure hn hc0.
have hKfinite := @compact_generator_scale_finite R X c delta nu K hX
  (compact_cost_nonnegative_law hc) hdpos hn hK.
have hSfinite : (nu S< +oo)%E := le_lt_trans (@measure_mono R X nu hm S K hSK) hKfinite.
have hfinite : nu S \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X nu hm S).
  exact hSfinite.
pose M := fine (nu S).
have hM : nu S=M%:E by rewrite /M fineK.
have hbM : b<M by move: hlower; rewrite hM lte_fin.
pose e := M-b.
have he : 0<e by rewrite /e subr_gt0.
pose xi := delta/2.
have hxipos : 0<xi by rewrite /xi divr_gt0 // ltr0n.
have hxid : xi<delta by rewrite /xi; lra.
have [C [hC [hCS hClower]]] := @compact_cost_suslin_bounded_approximation R X c hc delta xi e nu psi S K
  hX hdpos hxipos hxid he hn hpsi hK hSK hS.
have hh := le_trans hClower (hbound C hC hCS).
rewrite hM -EFinB lee_fin /e in hh.
have hstrict : b<M-(M-b)/2 by lra.
have hcontradiction := lt_le_trans hstrict hh; by rewrite ltxx in hcontradiction.
Qed.

(** Source for [compact_cost_suslin_mass_bound]: supporting
    removal of the compact-ambient reduction in
    2.10.23, p. 186. Closed-ball intersections
    remain Suslin and have compact containing sets;
    2.10.20 then gives the full mass bound. *)
Theorem compact_cost_suslin_mass_bound (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost c)
    (psi : set X -> \bar R) (S : set X) (b : R) :
  metric_boundedly_compact X ->
  is_caratheodory_limit (fun C : compact_metric_set X=>val C) (fun C=>(c C)%:E) psi ->
  is_suslin_set R S ->
  (forall C, compact C -> C `<=` S -> (psi C<=b%:E)%E) -> (psi S<=b%:E)%E.
Proof.
move=> hX hpsi hS hbound.
have hc0 C : (0<=(c C)%:E)%E by rewrite lee_fin; exact: (@compact_cost_nonnegative_law R X c hc C).
have hm := caratheodory_limit_is_measure hpsi hc0.
case: (pselect (S !=set0))=> [[a ha]|hempty].
- have hball r : measure_measurable psi (metric_closed_ball a r).
    have ho := closed_openC (@metric_closed_ball_closed R X a r).
    have hh := @caratheodory_limit_open_measurable R X (compact_metric_set X)
      (fun C=>val C) (fun C=>(c C)%:E) psi hpsi hc0 (~` metric_closed_ball a r) ho.
    have hhC := measure_measurable_complement hh; by rewrite setCK in hhC.
  have hradial := @measurable_ball_radial_continuity R X psi a S hm hball.
  have htrunc r : (psi (S `&` metric_closed_ball a r)<=b%:E)%E.
    pose K := metric_closed_ball a (Order.max r 0).
    have hr0 : 0<=Order.max r 0 by rewrite le_max lexx orbT.
    have hrmax : r<=Order.max r 0 by rewrite le_max lexx.
    have hK : compact K := hX a _ hr0.
    have hSK : S `&` metric_closed_ball a r `<=` K.
      move=> x [_ hxr]; exact: le_trans hxr hrmax.
    have hSus : is_suslin_set R (S `&` metric_closed_ball a r).
      apply: suslin_binary_intersection hS _; apply: metric_borel_suslin.
      exact: closed_borel_set (@metric_closed_ball_closed R X a r).
    apply: (@compact_cost_suslin_bounded_mass_bound R X c hc psi (S `&` metric_closed_ball a r) K b hX hpsi hK hSK hSus).
    move=> C hC hCS; apply: hbound hC _=> x hx; exact: (hCS x hx).1.
  rewrite leNgt; apply/negP=> hbad.
  have [r hr] := hradial.1 b%:E hbad.
  have hrr : r<r+1 by rewrite ltrDl ltr01.
  have hh := lt_le_trans (hr (r+1) hrr) (htrunc (r+1)); by rewrite ltxx in hh.
- have heq : S=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  have hh := hbound set0 (@compact0 X) (fun x hx=>False_ind _ hx).
  by rewrite heq (measure_empty hm) -(measure_empty hm) in hh *.
Qed.
