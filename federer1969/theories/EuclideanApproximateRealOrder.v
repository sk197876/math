(** Federer (1969), 3.1.3(4), p. 213: the finite approximate limit
    exists exactly when the two approximate order limits equal that value.
    This expands the good-locus argument using (2). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanApproximateContext CenteredBallRelations
  PartialFunctionUP PartialFunctionPostcomposition MeasureSetDensity
  MeasureApproximateLimitUP MeasureApproximateOrderLimits ExtendedRealOrderTopology
  MeasurableRealEmbedding LocalZeroDensity ApproximateOrderThresholdRays
  ApproximateLimitOrderValues ApproximateLimitComposition EuclideanZeroDensityUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section RealOrder.
Variable R : realType.
Variable k : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R k)).
Local Notation Leb := (@euclidean_lebesgue_measure R k).
Local Notation V := (@centered_closed_ball_relation R [the metricType R of E]).
Variable f : partial_function E (real_line_metric R).
Local Notation F := (partial_function_postcompose f (fun y : real_line_metric R=>
  (y%:E : extended_real_line R))).
Variable x : E.
Variable c : real_line_metric R.

(** Source for [euclidean_matching_order_limits_approximate_limit]:
    supporting converse used in the measurable set E of Federer
    3.1.3(4), p. 213. The two exceptional closed-ray complements have
    density-zero union, and trap every remaining function value in the
    prescribed real neighborhood. *)
Theorem euclidean_matching_order_limits_approximate_limit :
  measure_approximate_upper_limit Leb V F x=c%:E ->
  measure_approximate_lower_limit Leb V F x=c%:E ->
  is_measure_approximate_limit Leb V f x c.
Proof.
move=> hu hl W hn.
have [e he heW] := proj1 (metricType_numDomainType.nbhs_mdistP c W) hn.
have hupper : measure_approximate_upper_limit Leb V F x<(c+e)%R%:E.
  by rewrite hu lte_fin ltrDl.
have hlower : (c-e)%R%:E<measure_approximate_lower_limit Leb V F x.
  by rewrite hl lte_fin ltrBlDr ltrDl.
have [q [hqc hq]] := (approximate_upper_limit_rational_ray
  (euclidean_approximate_context R k) F x _).1 hupper.
have [p [hcp hp]] := (approximate_lower_limit_rational_ray
  (euclidean_approximate_context R k) F x _).1 hlower.
change (partial_function_graph (measure_set_density Leb V
  (~` partial_function_preimage F [set y | y<=(ratr q : R)%:E])) x 0) in hq.
change (partial_function_graph (measure_set_density Leb V
  (~` partial_function_preimage F [set y | (ratr p : R)%:E<=y])) x 0) in hp.
rewrite partial_function_postcompose_preimage in hq.
rewrite partial_function_postcompose_preimage in hp.
have hboth := euclidean_zero_density_union hq hp.
refine (@local_zero_density_mono R [the metricType R of E] Leb V
  (~` partial_function_preimage f W)
  ((~` partial_function_preimage f [set y | y%:E<=(ratr q : R)%:E]) `|`
   (~` partial_function_preimage f [set y | (ratr p : R)%:E<=y%:E]))
  setT x (euclidean_approximate_context R k) openT I _ hboth).
move=> z _ hz.
case: (pselect (partial_function_preimage f [set y | y%:E<=(ratr q : R)%:E] z))
  => [[u [huu huq]]|hnu]; last by left.
case: (pselect (partial_function_preimage f [set y | (ratr p : R)%:E<=y%:E] z))
  => [[v [hvv hpv]]|hnv]; last by right.
exfalso; apply: hz; exists u; split=> //; apply: heW.
have heuv := partial_function_single_valued huu hvv; rewrite -heuv in hpv.
have hqcR : (ratr q<c+e)%R := hqc.
have hcpR : (c-e<ratr p)%R := hcp.
have huqR : (u<=ratr q)%R := huq.
have hpvR : (ratr p<=u)%R := hpv.
change (is_true (`|c-u|<e)%R).
rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [euclidean_approximate_real_order_iff]: exact finite-value
    characterization supporting Federer 3.1.3(4), p. 213. It imposes
    neither measurability nor an artificial value at missing inputs. *)
Theorem euclidean_approximate_real_order_iff :
  is_measure_approximate_limit Leb V f x c <->
  measure_approximate_upper_limit Leb V F x=c%:E /\
  measure_approximate_lower_limit Leb V F x=c%:E.
Proof.
split; last by move=> [hu hl]; exact: euclidean_matching_order_limits_approximate_limit hu hl.
move=> hf.
have he := approximate_limit_continuous_postcompose (@real_extended_embedding_continuous R c) hf.
split.
- exact: (@approximate_limit_upper_value R [the metricType R of E] Leb V
    (euclidean_approximate_context R k) F x c%:E he).
- exact: (@approximate_limit_lower_value R [the metricType R of E] Leb V
    (euclidean_approximate_context R k) F x c%:E he).
Qed.
End RealOrder.
