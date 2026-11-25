(** Supporting countability for the Fubini applications in Federer (1969),
    2.6.3(2), pp. 117–118. Both factors are L^1 and are countably
    measurable, unlike example (1). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals PartialFunctionUP
  MeasureUP MeasurableFunctionUP CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableProduct ProductMeasure LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_real_zero_closed]: supporting
    closedness of zero in the order topology of Federer
    2.1.1, p. 51, for the nonzero-locus convention
    of 2.3.4, p. 76, used in 2.6.3(2),
    p. 118. Its complement is the union of two open rays. *)
Lemma extended_real_zero_closed (R : realType) :
  closed [set z : extended_real_line R | z=0].
Proof.
rewrite -openC.
have he : ~` [set z : extended_real_line R | z=0] =
    [set z : extended_real_line R | z < 0] `|` [set z : extended_real_line R | 0 < z].
  apply/seteqP; split=> z.
  - move=> hz; case: (ltgtP z 0)=> hh.
    + by left.
    + by right.
    + exact: False_ind (hz hh).
  - move=> [hz|hz] he; have heq : z=0 := he; subst z;
      have hbad : (0 : \bar R) < 0 := hz; by move: hbad; rewrite ?lte_fin ?ltxx.
rewrite he; apply: openU; [exact: order_strict_lower_ray_open | exact: order_strict_upper_ray_open].
Qed.

(** Source for [lebesgue_product_function_countably_measurable]: the
    countability premise for both Fubini applications in Federer 2.6.3(2),
    p. 118 Every measurable function on this whole countably measurable
    product has countably measurable nonzero locus. No integrability is
    asserted here. *)
Lemma lebesgue_product_function_countably_measurable (R : realType)
    (f : partial_function (R*R) (extended_real_line R)) :
  is_measure_measurable_function
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R)) f ->
  is_countably_measure_measurable_function
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (0 : extended_real_line R) f.
Proof.
move=> hf; apply: (countably_measurable_function_on_countable_source
  (product_measure_is_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
  (@extended_real_zero_closed R) _ hf).
exact: product_whole_countably_measurable (lebesgue_scalar_countably_measurable R) (lebesgue_scalar_countably_measurable R).
Qed.
