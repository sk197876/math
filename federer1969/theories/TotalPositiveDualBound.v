(** Federer (1969), 2.5.7, p. 98: the bound on the norm of a nonnegative
    candidate density follows from 2.4.16, pp. 89–90, by testing against
    nonnegative members of the conjugate unit ball. We retain all membership
    conditions and transfer the partial sign-matching tests to exact total
    graphs. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionSealed
  PartialScalarProduct MeasureUP CountablyMeasurableUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureDualTestUP ConjugateExponents MeasureFiniteDuality MeasureLoneDuality MeasureLinfinityDuality
  ExtendedRealBoundsUP TotalScalarLpUP TotalScalarTestTransfer TotalSignMatchingExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_total_pairing_bound]: the positive unit-ball
    testing estimate in the opening proof of Federer 2.5.7, p. 98 This
    predicate concerns actual signed integral values, with no convention
    assigned to an undefined integral. *)
Definition nonnegative_total_pairing_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) p (u : X -> R) M :=
  forall f, total_scalar_lp mu p f -> (forall x, (0 <= f x)%R) ->
    total_scalar_lp_norm mu p f <= 1 -> forall z,
    is_measure_integral mu (partial_scalar_product (total_scalar_function u) (total_scalar_function f)) z -> z <= M.

(** Source for [sign_matching_pairing_total_extension]: supporting
    exact integral transfer for the test restriction in Federer 2.5.7,
    p. 98, and 2.4.16, p. 89. The original domain
    is already total by equality of the partial sign functions. *)
Lemma sign_matching_pairing_total_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u : X -> R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) z :
  is_sign_matching_test (total_scalar_function u) f ->
  is_measure_integral mu (partial_scalar_product (total_scalar_function u) f) z ->
  is_measure_integral mu (partial_scalar_product (total_scalar_function u)
    (total_scalar_function (PartialFunctionExtension.value f 0%R))) z.
Proof.
move=> hs hi; apply: (@measure_integral_graph_equivalent R X mu _ _ z _ hi)=> x w.
rewrite !partial_scalar_product_graph; split.
- move=> [a [b [ha [hb hw]]]]; exists a,b; split=> //; split=> //.
  exact: (@sign_matching_total_extension_graph R X u f hs x b).1 hb.
- move=> [a [b [ha [hb hw]]]]; exists a,b; split=> //; split=> //.
  exact: (@sign_matching_total_extension_graph R X u f hs x b).2 hb.
Qed.

(** Source for [positive_finite_dual_values_bound]: reduction to nonnegative
    total tests in Federer 2.5.7, p. 98 Full sign matching forces a
    nonnegative test when the candidate density is nonnegative. *)
Lemma positive_finite_dual_values_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) (u : X -> R) M :
  (forall x, (0 <= u x)%R) -> nonnegative_total_pairing_bound mu p%:E u M ->
  forall z, sign_matching_finite_dual_values mu p (total_scalar_function u) z -> z <= M.
Proof.
move=> hu hb z [f [hf [hs hi]]].
have he := @sign_matching_total_extension_graph R X u f hs.
have [hmem hunit] := @finite_unit_test_total_transfer R X mu hm p f (PartialFunctionExtension.value f 0%R) hf he.
apply: (hb _ hmem _ hunit z).
- exact: (@sign_matching_extension_nonnegative R X u f hs hu).
- exact: (@sign_matching_pairing_total_extension R X mu u f z hs hi).
Qed.

(** Source for [positive_infinity_dual_values_bound]: the same reduction for
    the infinity test ball, supporting Federer 2.5.7, p. 98, using the p=1
    case of 2.4.16, p. 89 *)
Lemma positive_infinity_dual_values_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> R) M :
  (forall x, (0 <= u x)%R) -> nonnegative_total_pairing_bound mu +oo u M ->
  forall z, sign_matching_infinity_dual_values mu (total_scalar_function u) z -> z <= M.
Proof.
move=> hu hb z [f [hf [hs hi]]].
have he := @sign_matching_total_extension_graph R X u f hs.
have [hmem hunit] := @infinity_unit_test_total_transfer R X mu hm f (PartialFunctionExtension.value f 0%R) hf he.
apply: (hb _ hmem _ hunit z).
- exact: (@sign_matching_extension_nonnegative R X u f hs hu).
- exact: (@sign_matching_pairing_total_extension R X mu u f z hs hi).
Qed.

(** Source for [positive_finite_density_norm_bound]: the norm bound for
    finite q>1 in Federer 2.5.7, p. 98 This consequence also applies before
    finiteness of the candidate norm has been established. *)
Theorem positive_finite_density_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : R) (u : X -> R) M :
  (1 < q)%R -> (forall x, (0 <= u x)%R) ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function u) ->
  nonnegative_total_pairing_bound mu (finite_conjugate_exponent q)%:E u M ->
  total_scalar_lp_norm mu q%:E u <= M.
Proof.
move=> hq hu hc hb.
have hs := (@finite_dual_supremum R X mu hm q u hq hc).2.
apply: (@extended_real_supremum_least R _ _ hs).
exact: (@positive_finite_dual_values_bound R X mu hm (finite_conjugate_exponent q) u M hu hb).
Qed.

(** Source for [positive_lone_density_norm_bound]: the q=1 norm bound in
    case (iii) of Federer 2.5.7, p. 98 No sigma-finiteness of X is inserted:
    the candidate has countably measurable support. *)
Theorem positive_lone_density_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> R) M :
  (forall x, (0 <= u x)%R) ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function u) ->
  nonnegative_total_pairing_bound mu +oo u M -> total_scalar_lp_norm mu 1 u <= M.
Proof.
move=> hu hc hb.
have hs := (@lone_dual_supremum R X mu hm (total_scalar_function u) hc).2.
apply: (@extended_real_supremum_least R _ _ hs).
exact: (@positive_infinity_dual_values_bound R X mu hm u M hu hb).
Qed.

(** Source for [positive_linfinity_density_norm_bound]: the q=infinity norm
    bound in case (ii) of Federer 2.5.7, p. 98 The later existence argument
    must still supply the hypothesis that X is countably measurable. *)
Theorem positive_linfinity_density_norm_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> R) M :
  (forall x, (0 <= u x)%R) ->
  is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function u) ->
  nonnegative_total_pairing_bound mu 1 u M -> total_scalar_lp_norm mu +oo u <= M.
Proof.
move=> hu hc hb.
have hs := (@linfinity_dual_supremum R X mu hm u hc).2.
apply: (@extended_real_supremum_least R _ _ hs).
exact: (@positive_finite_dual_values_bound R X mu hm 1%R u M hu hb).
Qed.
