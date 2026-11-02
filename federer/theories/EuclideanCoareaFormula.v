(** Federer (1969), 3.2.11, pp. 248–249: the coarea
    formula for every Lebesgue-measurable subset of R^m.
    The proof follows the printed null-source, Borel, full-rank
    and critical-rank reductions. Apply erratum p. 5, book
    p. 249 line 21: the source measure is L^m(A). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanMeasurableBorelCore BorelCoarea
  CoareaNullSourceAgreement CoareaJacobianMeasure EuclideanTargetJacobianMeasurable
  LipschitzUP HausdorffMeasure MappingMultiplicity MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_coarea_formula]: Federer
    3.2.11, pp. 248–249: the integral of J_n f
    over A equals the Lebesgue integral of H^(m-n)
    of the fibres of A. This form identifies their
    common value with the already specified Jacobian measure,
    including infinite values and target dimension zero. *)
Theorem euclidean_coarea_formula (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) (euclidean_coarea_measure f A).
Proof.
move=>hnm hf hA.
have [C [hC [hCA hNull]]]:=euclidean_measurable_borel_core hA.
have hBorel:=borel_coarea hnm hf hC.
exact (coarea_null_source_integral_transfer (ltnW hnm) hf hCA hNull hBorel).
Qed.

(** Source for [federer_3_2_11]: the complete
    coarea theorem of Federer 3.2.11, pp. 248–249,
    under exactly m>n, Lipschitz f on R^m and
    Lebesgue-measurable A. Both actual integral graphs have
    the same value; no derivative default, Borelness,
    finite-mass or positive-target-dimension hypothesis is added. *)
Theorem federer_3_2_11 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (extended_euclidean_target_jacobian f) a /\
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
          :extended_real_line R))) a.
Proof.
move=>hnm hf hA; exists (euclidean_coarea_measure f A); split.
- exact (euclidean_coarea_measure_integral hf hA).
- exact (euclidean_coarea_formula hnm hf hA).
Qed.
