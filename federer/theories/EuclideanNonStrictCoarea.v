(** Federer (1969), 3.2.22, p. 260:
    use 3.2.11 for m>mu and the area formula
    at the boundary m=mu in the local chart comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue EuclideanAreaFormula EuclideanCoareaFormula
  EuclideanJacobianMeasurable EuclideanTargetJacobianMeasurable
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence HausdorffMeasure HausdorffCountingMeasure MappingMultiplicity ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_non_strict_coarea_formula]:
    the first local coarea equality in Federer 3.2.22,
    p. 260, including m=mu. The strict case
    is exactly 3.2.11, pp. 248–249. In equal
    dimensions 3.2.3(1), pp. 243–244, and the
    H^0 counting convention of 2.10.2, p. 171,
    identify fibre mass with mapping multiplicity. *)
Theorem euclidean_non_strict_coarea_formula (R:realType) m mu
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R mu)) A:
  (mu<=m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (extended_euclidean_target_jacobian f) a /\
    is_measure_integral (@euclidean_lebesgue_measure R mu)
      (partial_function_total (fun y=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R m)) (m-mu) (mapping_fibre f A y)
          :extended_real_line R))) a.
Proof.
move=>hDim hF hA.
have [hStrict|hGreater|hEqual]:=ltngtP mu m; first exact:(federer_3_2_11 hStrict hF hA).
- have hFalse:=leq_ltn_trans hDim hGreater; by rewrite ltnn in hFalse.
- subst mu.
  have [a [hSource hTarget]]:=euclidean_area_formula hF hA.
  exists a; split; first exact hSource.
  have hMeasures:(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) m)=
      (@euclidean_lebesgue_measure R m).
    apply:boolp.funext=>B; exact:(euclidean_hausdorff_spherical_lebesgue B).1.
  rewrite hMeasures in hTarget.
  apply:(measure_integral_graph_equivalent _ hTarget)=>y z.
  change (@mapping_multiplicity R _ _ f A y=z <->
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-m) (mapping_fibre f A y)=z).
  by rewrite subnn hausdorff_zero_counting_measure.
Qed.
