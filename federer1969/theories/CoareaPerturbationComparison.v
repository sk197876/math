(** Federer (1969), 3.2.11, p. 249: combine
    translation, Fubini and slicing for the critical perturbation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  CoareaPerturbationMap CoareaCylinderFibres CoareaTranslatedCutoff CoareaTranslatedProjectionBound
  CoareaProjectionFibreBound CoareaIteratedIntegralBound MappingMultiplicity HausdorffMeasure HausdorffFibreCost
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_perturbation_integral_comparison]:
    the integrated slicing inequality in Federer 3.2.11,
    p. 249. The two supplied integrals are the
    original and perturbed fibre masses; their geometric
    comparison is proved by the preceding exact fibre identities. *)
Theorem coarea_perturbation_integral_comparison (R:realType) m n
    (f:R_n R m->R_n R n) (e:R) A B a b:
  (n<=m)%N ->measure_measurable (@euclidean_lebesgue_measure R n) B ->0<=a ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) a ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (m+n))) m
      (mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y)
        :extended_real_line R))) b ->
  a*euclidean_lebesgue_measure n B<=
    (hausdorff_fibre_bound_constant (m-n) n (1:R))%:E*b.
Proof.
move=>hnm hB ha hi hg.
have hp y:0<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
    (m-n) (mapping_fibre f A y).
  exact (@measure_nonnegative R _ _ (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-n)) (mapping_fibre f A y)).
have hFubini:=(coarea_translated_cutoff_fubini e hB hp ha hi).2.
apply:(coarea_iterated_integral_upper_bound (euclidean_lebesgue_is_measure R n)
  (coarea_projection_fibre_coefficient_positive R (m-n) n) hFubini hg)=>y.
exact (@coarea_translated_projection_bound R m n f e A B y hnm).
Qed.
