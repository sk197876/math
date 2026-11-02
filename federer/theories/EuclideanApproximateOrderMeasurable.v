(** Federer (1969), 3.1.3(2), p. 213: approximate upper and lower
    limits of a jointly measurable function are measurable in the
    remaining parameter. The proof applies (1) to exceptional level
    sets and retains the exact partial domains prescribed by 2.9.12. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanApproximateContext CenteredBallRelations MeasureUP MeasureBasic
  MeasureSplit MeasureFiniteClosure MeasureCountableClosure MeasureAlmostBasic ProductMeasure ProductSections
  PartialFunctionBasic PartialProductSections MeasurableFunctionUP MeasurableFunctionBorel
  CountableOrderIntervals TopologicalBorel ExtendedRealOrderTopology
  MeasurableExtendedRationalRays MeasureApproximateOrderLimits
  ApproximateOrderThresholdRays EuclideanSectionDensityMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section Measurability.
Variable R : realType.
Variables m k : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb n := (@euclidean_lebesgue_measure R n).
Local Notation V := (@centered_closed_ball_relation R [the metricType R of E k]).
Local Notation ha := (euclidean_lebesgue_is_measure R m).
Local Notation hb := (euclidean_lebesgue_is_measure R k).
Variable f : partial_function (E m * E k) (extended_real_line R).
Hypothesis hf : is_measure_measurable_function (product_measure ha hb) f.

(** Source for [euclidean_approximate_upper_limit_measurable]: the
    approximate limsup assertion of Federer 3.1.3(2), p. 213. The
    supporting formulation also permits extended values and proper
    conull domains. Undefined section points belong to every exceptional
    set, consistently with the erratum to 2.9.12. *)
Theorem euclidean_approximate_upper_limit_measurable :
  @is_measure_measurable_function R _ [the topologicalType of extended_real_line R] (Leb m) (partial_function_total
    (fun x=>measure_approximate_upper_limit (Leb k) V
      (partial_product_vertical_section f x) (0%R : R_n R k))).
Proof.
apply/(measurable_extended_rational_lower_rays_iff ha).
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true ha.
- move=> t.
  have he : partial_function_preimage (partial_function_total
      (fun x=>measure_approximate_upper_limit (Leb k) V
        (partial_product_vertical_section f x) (0%R : R_n R k))) [set y | y<(ratr t : R)%:E]=
    \bigcup_(q in [set q : rat | (ratr q : R)%:E<(ratr t : R)%:E])
      [set x | measure_approximate_upper_thresholds (Leb k) V
        (partial_product_vertical_section f x) (0%R : R_n R k) (ratr q : R)%:E].
    apply/seteqP; split=> x.
    + move=> [y [<- hy]].
      have [q [hqt hq]] := (approximate_upper_limit_rational_ray
        (euclidean_approximate_context R k) (partial_product_vertical_section f x) (0%R : R_n R k) _).1 hy.
      by exists q.
    + move=> [q hqt hq]; exists (measure_approximate_upper_limit (Leb k) V
        (partial_product_vertical_section f x) (0%R : R_n R k)); split=> //.
      apply: (approximate_upper_limit_rational_ray
        (euclidean_approximate_context R k) (partial_product_vertical_section f x) (0%R : R_n R k) _).2.
      by exists q.
  rewrite he; apply: (measure_measurable_countable_union ha); first exact: countableP.
  move=> q _.
  have hpre := @measurable_function_borel_preimage R _
    [the topologicalType of extended_real_line R] (product_measure ha hb)
    (product_measure_is_measure ha hb) f hf [set y | y<=(ratr q : R)%:E]
    (closed_borel_set (@order_closed_lower_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E)).
  exact: euclidean_zero_density_section_measurable (measure_measurable_complement hpre).
Qed.

(** Source for [euclidean_approximate_lower_limit_measurable]: the
    approximate liminf assertion of Federer 3.1.3(2), p. 213. The same
    countable density-zero argument uses closed upper-ray complements. *)
Theorem euclidean_approximate_lower_limit_measurable :
  @is_measure_measurable_function R _ [the topologicalType of extended_real_line R] (Leb m) (partial_function_total
    (fun x=>measure_approximate_lower_limit (Leb k) V
      (partial_product_vertical_section f x) (0%R : R_n R k))).
Proof.
apply/(measurable_extended_rational_upper_rays_iff ha).
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true ha.
- move=> t.
  have he : partial_function_preimage (partial_function_total
      (fun x=>measure_approximate_lower_limit (Leb k) V
        (partial_product_vertical_section f x) (0%R : R_n R k))) [set y | (ratr t : R)%:E<y]=
    \bigcup_(q in [set q : rat | (ratr t : R)%:E<(ratr q : R)%:E])
      [set x | measure_approximate_lower_thresholds (Leb k) V
        (partial_product_vertical_section f x) (0%R : R_n R k) (ratr q : R)%:E].
    apply/seteqP; split=> x.
    + move=> [y [<- hy]].
      have [q [htq hq]] := (approximate_lower_limit_rational_ray
        (euclidean_approximate_context R k) (partial_product_vertical_section f x) (0%R : R_n R k) _).1 hy.
      by exists q.
    + move=> [q htq hq]; exists (measure_approximate_lower_limit (Leb k) V
        (partial_product_vertical_section f x) (0%R : R_n R k)); split=> //.
      apply: (approximate_lower_limit_rational_ray
        (euclidean_approximate_context R k) (partial_product_vertical_section f x) (0%R : R_n R k) _).2.
      by exists q.
  rewrite he; apply: (measure_measurable_countable_union ha); first exact: countableP.
  move=> q _.
  have hpre := @measurable_function_borel_preimage R _
    [the topologicalType of extended_real_line R] (product_measure ha hb)
    (product_measure_is_measure ha hb) f hf [set y | (ratr q : R)%:E<=y]
    (closed_borel_set (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E)).
  exact: euclidean_zero_density_section_measurable (measure_measurable_complement hpre).
Qed.
End Measurability.
