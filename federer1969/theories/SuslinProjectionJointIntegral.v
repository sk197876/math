(** Supporting Suslin-source extension of Federer (1969), 2.10.16, p. 178,
    for the projected images appearing in its further slicing identities.
    The actual joint count remains the same sealed counting measure of the
    fibres. Source context and scalar convergence references:
    ProjectionJointMultiplicity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  EuclideanLebesgueDimensions OrthogonalProjectionProbability ProjectionBeta IntegralGeometricMeasure
  ProjectionJointMultiplicity ProjectionMultiplicityIntegral IntegralGeometricMultiplicity
  ExtendedRealOrderTopology PartialFunctionBasic PartialProductSections PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureNonnegativeIntegral
  ProductMeasure ProductFunctionFubini CountablyMeasurableUP CountablyMeasurableBasic
  CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  ParameterizedIntegral MappingMultiplicity ProjectionJointMultiplicityIntegral
  SuslinProjectionJointMultiplicity SuslinProjectionMultiplicity
  SuslinIntegralGeometricMultiplicity SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_joint_suslin_multiplicity_integral]: supporting
    Suslin-source product-integral form supporting 2.10.16, p. 178.
    Joint measurability and nonnegativity give an actual integral;
    Fubini identifies its value with beta_1 I_1(A), including
    infinity. The inner section integrals are the actual g(p). *)
Theorem projection_joint_suslin_multiplicity_integral (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R A ->
  is_measure_integral (@projection_product_measure R n m hmn)
    (partial_function_total (projection_joint_multiplicity (m:=m) A))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A).
Proof.
move=> hA.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := orthogonal_projection_metric_space R n m.
pose theta := @orthogonal_projection_probability R n m hmn.
pose mu := @projection_product_measure R n m hmn.
pose f := partial_function_total (projection_joint_multiplicity (m:=m) A).
have hm := @projection_product_measure_is_measure R n m hmn.
have hf := @projection_joint_suslin_multiplicity_measurable R n m hmn A hA.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R [the choiceType of ((Y*P)%type)] mu hm
    setT _ _ (measure_almost_everywhere_true hm))=> z _.
  exists (projection_joint_multiplicity A z); split=> //; exact: projection_joint_multiplicity_nonnegative.
have [hi _] := @nonnegative_measurable_function_integral R [the choiceType of ((Y*P)%type)] mu hm f hf hp.
pose J := measure_lower_integral mu f.
have hc : is_countably_measure_measurable_function mu (0 : extended_real_line R) f.
  exact: (@countably_measurable_function_on_countable_source R [the choiceType of ((Y*P)%type)]
    (extended_real_line R) mu hm 0 f (@extended_real_zero_closed R)
    (@projection_product_whole_countably_measurable R n m hmn) hf).
have hiP := (@product_function_fubini R Y P (@euclidean_lebesgue_measure R m) theta
  (@euclidean_lebesgue_is_measure R m) (@theta_star_is_measure R n m hmn) f J hi hc).2.
have hiG : is_measure_integral theta
    (partial_function_total (projection_multiplicity_integral (m:=m) A)) J.
  apply: (@measure_integral_graph_equivalent R P theta _ _ J _ hiP)=> p z.
  rewrite parameterized_integral_specification.
  change (is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A p) z <-> projection_multiplicity_integral A p=z).
  have hsec := @projection_multiplicity_suslin_integral_specification R n m A p hA.
  split.
  - move=> hz; exact: esym (measure_integral_unique hz hsec).
  - move=> hz; by rewrite -hz.
have hbook := (@suslin_integral_geometric_multiplicity_integral R n m hmn A hA).
have he := measure_integral_unique hiG hbook.
have hiJ : is_measure_integral mu f J := hi.
by rewrite he in hiJ.
Qed.
