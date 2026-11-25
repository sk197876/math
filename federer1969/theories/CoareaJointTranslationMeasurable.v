(** Federer (1969), 3.2.11, p. 249: the joint
    measurability used before interchanging the two integrals.
    The scaled translation is pulled back through an actual
    linear epimorphism, using 3.1.3(3). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates CoareaPerturbationLinear EuclideanEpimorphismNull
  EuclideanBlockMeasurableFunctions EuclideanLebesgueDimensions ProductMeasure
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasurableFunctionUP MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [coarea_joint_scaled_translation_measurable]:
    the measurable integrand theta(y-epsilon*z) in Federer
    3.2.11, p. 249. No Borel representative of theta
    is required, and the result includes epsilon=0. *)
Lemma coarea_joint_scaled_translation_measurable (R:realType) n (Y:topologicalType)
    (f:inner_metric_space (@euclidean_inner_productP R n)->Y) (e:R):
  is_measure_measurable_function (@euclidean_lebesgue_measure R n) (partial_function_total f) ->
  is_measure_measurable_function
    (product_measure (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R n))
    (partial_function_total (fun yz=>f (yz.1-e*:yz.2))).
Proof.
move=>hf.
pose D:=hom_of_linear (linear_id (R_n R n)).
pose p:=hom_as_linear (coarea_perturbation_linear D (-e)).
have hp:forall y,exists w,p w=y.
  move=>y; exists (euclidean_block_join (y,0)).
  change (coarea_perturbation_linear D (-e) (euclidean_block_join (y,0))=y).
  by rewrite coarea_perturbation_linear_pair hom_of_linearE scaler0 addr0.
have hh:=euclidean_block_join_measurable_precompose
  (euclidean_epimorphism_measurable_precompose (p:=p) hp hf).
apply:(measurable_function_graph_equivalent _ hh)=> -[y z] t.
change (f (coarea_perturbation_linear D (-e) (euclidean_block_join (y,z)))=t <->
  f (y-e*:z)=t).
by rewrite coarea_perturbation_linear_pair hom_of_linearE scaleNr.
Qed.
