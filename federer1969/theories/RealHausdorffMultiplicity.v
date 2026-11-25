(** Federer 2.10.11, p. 176, in every nonnegative real degree.
    Reuse the multiplicity identity of 2.10.10, Borel image measurability,
    and the existing Borel Caratheodory comparison. The real-degree image
    bound supplies the only dimensional input. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  BorelRegularMeasureUP BorelImageMeasurability TopologicalBorel CompleteMetricUP
  LipschitzUP LipschitzConstant NormMetricScaleContinuity RealPower
  RealHausdorffMeasure RealHausdorffLipschitz
  BorelImageCoverCost BorelCaratheodoryMeasure BorelCaratheodoryMeasureBound
  BorelMultiplicityIntegral MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_borel_multiplicity_comparison]: supporting
    assembly for Federer 2.10.11, p. 176, from 2.10.10. An arbitrary
    nonnegative image-measure comparison bounds the multiplicity
    integral. Completeness and separability give image measurability;
    target completeness and separability are not required. *)
Theorem continuous_borel_multiplicity_comparison (R : realType)
    (X Y : metricType R) (f : X -> Y) (mu : set X -> \bar R)
    (beta : set Y -> \bar R) (a : R) (D A : set X) :
    is_complete_metric_space X -> countable D -> dense D ->
    is_measure mu -> is_borel_regular_measure mu ->
    is_measure beta -> is_borel_regular_measure beta ->
    continuous f -> (0<=a)%R ->
    (forall B, borel_set B -> beta (f @` B)<=a%:E*mu B) ->
    borel_set A ->
    let F := partial_function_total
      (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)) in
    is_measure_integral beta F (measure_lower_integral beta F) /\
      measure_lower_integral beta F<=a%:E*mu A.
Proof.
move=> hX hD hden hm hr hb hrb hf ha hcost hA F.
have hImage S : borel_set S -> measure_measurable beta (f @` S).
  exact: (@continuous_borel_image_measurable R X Y f beta hb S hX
    (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y) hf
    (fun C hC => @borel_regular_borel_measurable R Y beta hb hrb C
      (closed_borel_set hC))).
have hi := @borel_multiplicity_integral R X Y f beta hb D A hD hden hImage hA.
pose c := borel_image_cover_cost f beta.
have he : measure_lower_integral beta F=borel_caratheodory_measure c A.
  exact: (@measure_lower_integral_unique R Y beta F _ _
    (measure_lower_integral_specification beta F) hi.2.2).
split; first by rewrite he.
rewrite he.
exact: (@borel_caratheodory_measure_bound R X c
  (@borel_image_cover_cost_laws R X Y f beta hb) mu hm hr D a
  hD hden ha hcost A).
Qed.

(** Source for [lipschitz_real_hausdorff_multiplicity_bound]: direct
    real-degree Hausdorff assertion of Federer 2.10.11, p. 176, with
    any finite Lipschitz bound. Integral existence and its sharp bound
    hold at every original 0<=m<infinity, including zero degree and
    zero Lipschitz bound. Both measures have the actual Gamma coefficient. *)
Theorem lipschitz_real_hausdorff_multiplicity_bound (R : realType)
    (X Y : metricType R) (f : X -> Y) (L p : R) (hp : (0<=p)%R)
    (D A : set X) :
    is_complete_metric_space X -> countable D -> dense D ->
    is_metric_lipschitz_bound setT f L -> borel_set A ->
    let beta := @real_hausdorff_measure R Y p hp in
    let F := partial_function_total
      (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)) in
    is_measure_integral beta F (measure_lower_integral beta F) /\
      measure_lower_integral beta F<=
        (real_power L p)%:E * @real_hausdorff_measure R X p hp A.
Proof.
move=> hX hD hden hf hA beta F.
apply: (@continuous_borel_multiplicity_comparison R X Y f
  (@real_hausdorff_measure R X p hp)
  beta (real_power L p) D A hX hD hden
  (@real_hausdorff_measure_is_measure R X p hp)
  (@real_hausdorff_measure_borel_regular R X p hp)
  (@real_hausdorff_measure_is_measure R Y p hp)
  (@real_hausdorff_measure_borel_regular R Y p hp) _
  (real_power_nonnegative L p) _ hA).
- apply: (@metric_fixed_lipschitz_continuous R X Y f L hf.1)=> x y.
  exact: hf.2 x y I I.
- move=> B _; exact: (@real_hausdorff_lipschitz_image_bound R X Y f L p hp hf B).
Qed.

(** Source for [federer_2_10_11_real_hausdorff]: direct Hausdorff
    conclusion of Federer 2.10.11, p. 176, with the original least
    constant Lip(f), arbitrary nonnegative real degree, and the original
    complete separable source and Borel source subset hypotheses. *)
Corollary federer_2_10_11_real_hausdorff (R : realType)
    (X Y : metricType R) (f : X -> Y)
    (hlip : is_metric_lipschitz setT f) (p : R) (hp : (0<=p)%R)
    (D A : set X) :
    is_complete_metric_space X -> countable D -> dense D -> borel_set A ->
    let beta := @real_hausdorff_measure R Y p hp in
    let F := partial_function_total
      (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R)) in
    is_measure_integral beta F (measure_lower_integral beta F) /\
      measure_lower_integral beta F<=
        (real_power (metric_lipschitz_constant hlip) p)%:E*
          @real_hausdorff_measure R X p hp A.
Proof.
move=> hX hD hden hA.
exact: (@lipschitz_real_hausdorff_multiplicity_bound R X Y f
  (metric_lipschitz_constant hlip) p hp D A hX hD hden
  (least_metric_lipschitz_bound (metric_lipschitz_constant_specification hlip)) hA).
Qed.
