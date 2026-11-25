(** Federer (1969), 2.6.2(4), p. 117: null modifications preserve iterated
    integrals. This supporting transfer uses the exact inner-integrability
    graphs, not arbitrary values at nonintegrable parameters. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality
  ParameterizedIntegralUP ParameterizedIntegral ProductMeasure PartialProductSections ProductSectionsAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [parameterized_integral_almost_equal_family]:
    supporting actual-inner-integral transfer for Federer 2.6.2(4),
    p. 117. On the conull domain of the first
    outer integrand, the second has the same integral value. *)
Lemma parameterized_integral_almost_equal_family (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f g : X -> partial_function Y (extended_real_line R)) a :
  measure_almost_everywhere alpha [set x | measure_almost_equal beta (f x) (g x)] ->
  is_measure_integral alpha (parameterized_integral beta f) a ->
  is_measure_integral alpha (parameterized_integral beta g) a.
Proof.
move=> he hi; apply: (@measure_integral_almost_equal R X alpha ha _ _ _ hi).
apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _
  (@measure_almost_everywhere_and R X alpha ha _ _ he (measurable_function_domain hi.1))).
move=> x [hx [z hz]]; exists z; split=> //.
apply: (parameterized_integral_specification beta g x z).2.
exact (@measure_integral_almost_equal R Y beta hb (f x) (g x) z
  ((parameterized_integral_specification beta f x z).1 hz) hx).
Qed.

(** Source for [product_iterated_integral_almost_equal]: supporting
    partial-domain reduction in Federer 2.6.2(4), p. 117,
    using the null-section case of (3). *)
Lemma product_iterated_integral_almost_equal (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f g : partial_function (X * Y) (extended_real_line R)) a :
  measure_almost_equal (product_measure ha hb) f g ->
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) a ->
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section g)) a.
Proof.
move=> he hi; exact (@parameterized_integral_almost_equal_family R X Y alpha beta ha hb _ _ a
  (@product_almost_equal_vertical_sections R X Y (extended_real_line R) alpha beta ha hb f g he) hi).
Qed.
