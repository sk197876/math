(** Integer-degree core of Federer (1969), 2.10.11, p. 176: combine the
    multiplicity identity of 2.10.10 with the actual Hausdorff image bound
    and the Borel- partition measure comparison. Completeness and
    separability of the source discharge image measurability through 2.2.13,
    pp. 69–70. The target need not be complete or separable. The optional
    real-degree extension and the spherical variant remain separate
    obligations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness BorelRegularMeasureUP
  BorelImageMeasurability TopologicalBorel CompleteMetricUP
  LipschitzUP LipschitzConstant NormMetricScaleContinuity HausdorffLipschitzImages
  HausdorffMeasure HausdorffClosedCoverAgreement BorelImageCoverCost BorelCaratheodoryMeasure
  BorelCaratheodoryMeasureBound BorelMultiplicityIntegral MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lipschitz_hausdorff_multiplicity_integer_bound]:
    direct integer-degree Hausdorff multiplicity estimate of
    Federer 2.10.11, p. 176, with any finite Lipschitz bound
    L. Existence of the integral and the inequality are both
    proved. Includes zero degree and zero Lipschitz bound. *)
Theorem lipschitz_hausdorff_multiplicity_integer_bound (R : realType)
    (X Y : metricType R) (f : X -> Y) (L : R) (m : nat) (D A : set X) :
  is_complete_metric_space X -> countable D -> dense D ->
  is_metric_lipschitz_bound setT f L -> borel_set A ->
  let beta := @hausdorff_measure R Y m in
  let F := partial_function_total (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)) in
  is_measure_integral beta F (measure_lower_integral beta F) /\
  measure_lower_integral beta F<=(L^+m)%R%:E* @hausdorff_measure R X m A.
Proof.
move=> hX hD hden hf hA beta F.
have hb : is_measure beta := @hausdorff_measure_is_measure R Y m.
have hrb : is_borel_regular_measure beta := @hausdorff_measure_borel_regular R Y m.
have hcont : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f L hf.1)=> x y; exact: hf.2 x y I I.
have hImage S : borel_set S -> measure_measurable beta (f @` S).
  exact: (@continuous_borel_image_measurable R X Y f beta hb S hX
    (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y) hcont
    (fun C hC => @borel_regular_borel_measurable R Y beta hb hrb C (closed_borel_set hC))).
have hi := @borel_multiplicity_integral R X Y f beta hb D A hD hden hImage hA.
pose c := borel_image_cover_cost f beta.
have he : measure_lower_integral beta F=borel_caratheodory_measure c A.
  exact: (@measure_lower_integral_unique R Y beta F _ _ (measure_lower_integral_specification beta F) hi.2.2).
split; first by rewrite he.
rewrite he.
apply: (@borel_caratheodory_measure_bound R X c (@borel_image_cover_cost_laws R X Y f beta hb)
  (@hausdorff_measure R X m) (@hausdorff_measure_is_measure R X m)
  (@hausdorff_measure_borel_regular R X m) D (L^+m)%R hD hden _ _ A).
- exact: exprn_ge0 hf.1.
- move=> B _; exact: (@hausdorff_lipschitz_image_bound R X Y f L m hf B).
Qed.

(** Source for [federer_2_10_11_integer]: integer-degree
    specialization of Federer 2.10.11, p. 176, using the
    actual least constant Lip(f) of 2.2.7, p. 64. This
    name explicitly excludes the pending real-degree and
    spherical-measure extensions of the printed item. *)
Corollary federer_2_10_11_integer (R : realType) (X Y : metricType R)
    (f : X -> Y) (hlip : is_metric_lipschitz setT f) (m : nat) (D A : set X) :
  is_complete_metric_space X -> countable D -> dense D -> borel_set A ->
  let beta := @hausdorff_measure R Y m in
  let F := partial_function_total (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)) in
  is_measure_integral beta F (measure_lower_integral beta F) /\
  measure_lower_integral beta F<=((metric_lipschitz_constant hlip)^+m)%R%:E*
    @hausdorff_measure R X m A.
Proof.
move=> hX hD hden hA.
exact: (@lipschitz_hausdorff_multiplicity_integer_bound R X Y f (metric_lipschitz_constant hlip) m D A
  hX hD hden (least_metric_lipschitz_bound (metric_lipschitz_constant_specification hlip)) hA).
Qed.
