(** Federer (1969), 3.2.11, p. 249: Rademacher
    removes the null complement of the actual differential
    domain. The preceding rank cases give coarea on what remains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanLipschitzClassZero TopologicalBorel BorelFamilyBasic
  DifferentialRankLociBorel DifferentiableBorelCoarea CoareaNullSourceAgreement CoareaJacobianMeasure
  Rademacher NormDifferentialUP LipschitzUP HausdorffMeasure MappingMultiplicity
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP PartialFunctionUP PartialFunctionBasic
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_coarea]: the Borel-source case
    of Federer 3.2.11, p. 249. Almost-everywhere
    differentiability is derived from Lipschitzness, including n=0;
    no differentiability premise or total Jacobian default is added. *)
Theorem borel_coarea (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<m)%N ->is_metric_lipschitz setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) (euclidean_coarea_measure f A).
Proof.
move=>hnm hf hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose F:set X:=[set x|norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R n)) setT f x].
pose C:=A `&`F.
have hFB:borel_set F:=ordinary_differential_locus_borel (euclidean_lipschitz_norm_class_zero hf).
have hCB:borel_set C:=borel_family_binary_intersection (borel_sets_family X) hA hFB.
have hDiff:=federer_3_1_6 hf.
have hNull:mu (A `\` C)=0.
  apply:(measure_null_subset hm _ hDiff)=>x [hx hn].
  by move=>hF; apply:hn; split.
have hCFormula:=differentiable_borel_coarea hnm hf hCB (fun x (hx:C x)=>hx.2).
exact (coarea_null_source_integral_transfer (ltnW hnm) hf (fun x (hx:C x)=>hx.1) hNull hCFormula).
Qed.
