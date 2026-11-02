(** Federer (1969), 2.6.2(4), proof p. 117: complete the nonnegative proof
    using the positive/negative-part identity 2.4.4(6), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPostcomposition MeasureUpperIntegralPositivePart PartialFunctionIntegralParts PartialExtendedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralNegation MeasureIntegralNegationLaw MeasureIntegralAddition
  MeasureIntegralAlmostEquality MeasureIntegralPartsDifference ParameterizedIntegralUP ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [parameterized_integral_from_parts]: supporting
    final signed step of Federer 2.6.2(4), p. 117,
    using 2.4.4(6), p. 82. The defined global
    difference supplies a conull domain where the inner difference
    is defined. Infinity minus infinity is never assigned a value. *)
Lemma parameterized_integral_from_parts (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> partial_function Y (extended_real_line R)) P N a :
  is_measure_integral alpha (parameterized_integral beta (fun x => partial_extended_function_positive_part (f x))) P ->
  is_measure_integral alpha (parameterized_integral beta (fun x => partial_extended_function_negative_part (f x))) N ->
  extended_subtract P N = Some a ->
  is_measure_integral alpha (parameterized_integral beta f) a.
Proof.
move=> hp hn hdiff.
pose gp := parameterized_integral beta (fun x => partial_extended_function_positive_part (f x)).
pose gn := parameterized_integral beta (fun x => partial_extended_function_negative_part (f x)).
pose d := partial_extended_function_subtract gp gn.
have hneg := @measure_integral_negation R X alpha ha gn N hn.
have hd : is_measure_integral alpha d a := @measure_integral_add R X alpha ha gp
  (partial_extended_function_negate gn) P (-N) a hp hneg hdiff.
apply: (@measure_integral_almost_equal R X alpha ha d _ a hd).
apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ (measurable_function_domain hd.1)).
move=> x [z hz]; exists z; split=> //.
apply: (parameterized_integral_specification beta f x z).2.
have [p [q [hpx [[n [hnx enq]] he]]]] :=
  (@partial_extended_function_add_graph R X gp
    (partial_extended_function_negate gn) x z).1 hz.
have hip := (parameterized_integral_specification beta (fun x => partial_extended_function_positive_part (f x)) x p).1 hpx.
have hin := (parameterized_integral_specification beta (fun x => partial_extended_function_negative_part (f x)) x n).1 hnx.
apply: (@measure_integral_from_parts R Y beta hb (f x) p n z hip hin).
by rewrite /extended_subtract enq.
Qed.
