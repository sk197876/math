(** Federer (1969), 3.1.16, p. 228: compact Lipschitz restrictions C_i
    with a summable measure defect in the open annuli about the origin. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanClosedBallCompact
  EuclideanSphereNull EuclideanApproximateContext CenteredBallRelations
  ApproximateMetricGrowth MeasureApproximateOrderLimits ApproximateGrowthDifferentiability
  CountableFamilySequence MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureCountableClosure MeasureSplit BorelRegularMeasureUP TopologicalBorel
  MetricClosedBalls OpenAnnuliClosedUnion GeometricErrorBudget MeasureGeometricCover
  MeasurableLipschitzCompactPiece.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_approximate_growth_annular_compacts]: the compact
    sets C_i in the first paragraph of the proof of Federer 3.1.16,
    p. 228. Geometric error budgets leave a strict total bound. The null
    integer spheres account for the omitted boundaries of the annuli. *)
Theorem finite_approximate_growth_annular_compacts (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) (e : R) :
  (forall a, A a -> (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m.+1)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
    (partial_metric_growth_quotient A f a) a< +oo)%E) -> 0<e ->
  exists C : nat->set (inner_metric_space (@euclidean_inner_productP R m.+1)),
    (forall i, compact (C i) /\ C i `<=` A `&` open_annulus (0 : inner_metric_space (@euclidean_inner_productP R m.+1)) i /\ is_metric_lipschitz (C i) f) /\
    (@euclidean_lebesgue_measure R m.+1 (A `\` \bigcup_i C i)<e%:E)%E.
Proof.
move=>hg he.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
have [F [hF [hcover _]]] := federer_3_1_8 hg.
have hA : measure_measurable mu A.
  rewrite hcover.
  exact (@measure_measurable_countable_union R X [the choiceType of ((nat*nat)%type : Type)] mu hm setT F (countableP _) (fun i _=>(hF i).1)).
have [E [hE hEU]] := @countable_family_as_sequence X [the choiceType of ((nat*nat)%type : Type)] setT F (countableP _).
have hEm i : measure_measurable mu (E i) /\ is_metric_lipschitz (E i) f.
  case: (hE i)=>[->|[p [_ ->]]].
  - split; first exact: measure_measurable_empty hm.
    exact: metric_lipschitz_of_bound (least_metric_lipschitz_bound (@metric_lipschitz_empty R X Y f)).
  - by split; [exact (hF p).1|exact (hF p).2.2].
have hAE : A `<=` \bigcup_i E i by rewrite hEU -hcover.
pose U i := open_annulus (0:X) i.
have hUm i : measure_measurable mu (U i).
  exact (borel_regular_open_measurable (euclidean_lebesgue_borel_regular R m.+1) (open_annulus_open (0:X) i)).
have hUball i : U i `<=` metric_closed_ball (0:X) (i.+1%:R : R).
  by move=>x /andP [_ hx]; exact: ltW hx.
have hex i : exists C, compact C /\ C `<=` A `&` U i /\ is_metric_lipschitz C f /\
    (mu ((A `&` U i) `\` C)<(geometric_error_budget e i)%:E)%E.
  apply: (@measurable_lipschitz_compact_piece R X Y mu hm
    (euclidean_lebesgue_borel_regular R m.+1) (A `&` U i)
    (metric_closed_ball (0:X) (i.+1%:R : R)) E f (geometric_error_budget e i)).
  - exact: euclidean_closed_metric_ball_compact.
  - by move=>x [_ hx]; exact: hUball i x hx.
  - exact: (@measure_measurable_intersection R X mu hm _ _ hA (hUm i)).
  - apply: le_lt_trans (measure_mono hm _) (euclidean_compact_finite (@euclidean_closed_metric_ball_compact R m.+1 0 i.+1%:R)).
    by move=>x [_ hx]; exact: hUball i x hx.
  - exact hEm.
  - by move=>x [hx _]; exact: hAE.
  - exact: geometric_error_budget_positive i he.
have [C hC] := choice hex.
exists C; split; first by move=>i; split; [exact (hC i).1|split; [exact (hC i).2.1|exact (hC i).2.2.1]].
pose D i := (A `&` U i) `\` C i.
have hsum : (mu (\bigcup_i D i)<=(e/2)%:E)%E.
  exact: (@measure_geometric_cover_bound R X mu hm (\bigcup_i D i) D e he (fun x hx=>hx) (fun i=>(hC i).2.2.2)).1.
have hcov : A `\` \bigcup_i C i `<=` (~`\bigcup_i U i) `|` (\bigcup_i D i).
  move=>x [hx hn]; case: (pselect ((\bigcup_i U i) x))=>[[i _ hi]|hnU]; last by left.
  right; exists i=>//; split; first by split.
  by move=>hc; apply: hn; exists i.
have hb := measure_binary_cover hm hcov.
rewrite (euclidean_annuli_complement_null R m) add0e in hb.
apply: le_lt_trans (le_trans hb hsum) _.
by rewrite lte_fin; lra.
Qed.
