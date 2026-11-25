(** Federer (1969), 3.1.7, p. 217: approximate
    differentiability and approximate partial derivatives of Lipschitz
    maps on arbitrary Lebesgue-measurable domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanLebesgueDimensions EuclideanApproximateContext EuclideanCoordinateSectionDensity
  RealNormUP NormDifferentialUP NormPartialDerivative
  OrdinaryDifferentialOnDensityDomain OrdinaryPartialOnDensityDomain
  ApproximateDifferential ApproximatePartialDerivative LipschitzUP
  KirszbraunTheorem Rademacher PartialFunctionUP MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureDensityPoints DensityMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [federer_3_1_7]: the whole lemma in Federer
    3.1.7, p. 217. A sealed global Kirszbraun extension
    supplies the differential through 3.1.6; density-one domain
    and section points transfer it to the actual domain A.
    Positive source dimension retains the punctured-quotient
    convention of 3.1.2; the target dimension may be zero. *)
Theorem federer_3_1_7 (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  measure_measurable (@euclidean_lebesgue_measure R m.+1) A ->
  is_metric_lipschitz A f ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) A
    [set a | exists L : Hom (R_n R m.+1) (R_n R n),
      partial_function_graph
        (approximate_differential
          (inner_norm_real_norm (@euclidean_inner_productP R n)) A f) a L /\
      forall i : 'I_m.+1, partial_function_graph
        (approximate_partial_derivative
          (inner_norm_real_norm (@euclidean_inner_productP R n)) A f i)
        a (L (@coordinate_basis R m.+1 i))].
Proof.
move=> hA hLip.
have [g [hGlobal [hag _]]] := federer_2_10_43 hLip.
have hfg x : A x -> f x=g x by move=> hx; exact: esym (hag x hx).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m.+1).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
have hdiff := federer_3_1_6 hGlobal.
have hden := (density_complement_zero_points_conclusions A
  (euclidean_approximate_context R m.+1)).2.2.2.1 hA.
have hdenimp := (measure_almost_everywhere_on_implication _ _ _).1 hden.
have hlines : measure_almost_everywhere mu
    (\bigcap_i [set a | A a -> coordinate_section_complement_zero_density A i a]).
  apply: (measure_almost_everywhere_countable hm); first exact: countableP.
  move=> i _; apply: (measure_almost_everywhere_on_implication _ _ _).1.
  exact (@coordinate_section_density_almost_everywhere R m.+1 A i hA).
have hall := measure_almost_everywhere_and hm hdiff
  (measure_almost_everywhere_and hm hdenimp hlines).
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono hm _ hall)=> a [[L hL] [hda hla]] ha.
exists L; split.
- apply: (approximate_differential_graph hNY A f a L).2.
  exact: (ordinary_differential_on_density_domain hNY hfg ha (hda ha) hL).
- move=> i; apply: (approximate_partial_derivative_graph hNY A f i a _).2.
  apply: (ordinary_partial_on_density_domain hNY hfg ha).
  + exact: coordinate_section_density_scalar (hla i Logic.I ha).
  + exact: (norm_differential_partial hNX hNY hL i).
Qed.
