(** Federer (1969), 4.1.5, p. 350:
    extend the original weak-dual field by zero
    only to apply the localized Euclidean
    differentiation theorem. Its original values
    and unit bound are retained. Measurability
    is for the actual image measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ContinuousDualUP ContinuousDualNorm WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp CompactContinuousVectorZeroExtension PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition MeasureUP MeasurePushforward MeasurableFunctionUP MeasurableGraphEquivalence
  PushforwardMeasurableFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenSubspaceWeakDualExtension.
Variable R:realType.
Variable T:topologicalType.
Variable U:set T.
Local Notation X := (set_type U).
Variable Y D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable xi:X->D.
Local Notation W := (@compact_vector_open_extension R T U D xi).

(** Source for [subspace_weak_dual_zero_extension_measurable]:
    the actual original weak field, extended by
    zero, is measurable for the inclusion image
    measure, supporting Federer 4.1.5, p. 350. *)
Theorem subspace_weak_dual_zero_extension_measurable (O:set (set D))
    (hO:is_weak_evaluation_topology (fun a y=>ed a y) O) (mu:set X->\bar R):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))) ->
  is_measure_measurable_function (measure_pushforward (fun x:X=>(set_val x:T)) mu)
    (partial_function_total (fun x=>(W x:open_family_topological_space hO.1))).
Proof.
move=>hXi.
apply:(@pushforward_function_measurable_from_composition R X T (open_family_topological_space hO.1)
  mu (fun x:X=>(set_val x:T)) (partial_function_total (fun x=>(W x:open_family_topological_space hO.1)))).
apply:(@measurable_function_graph_equivalent R X (open_family_topological_space hO.1) mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))) _ _ hXi)=>x z.
rewrite /partial_function_precompose /=.
change (xi x=z <->W (set_val x)=z).
by rewrite compact_vector_open_extension_value.
Qed.

(** Source for [subspace_unit_dual_zero_extension_bound]:
    zero extension preserves the original unit
    dual bound in the localized proof of
    Federer 4.1.5, p. 350. *)
Theorem subspace_unit_dual_zero_extension_bound (NY:Y->R) (hNY:is_real_norm NY)
    (DN:D->R) (hD:is_continuous_dual hNY ed DN):
  (forall x,DN (xi x)<= 1) ->forall x,DN (W x)<= 1.
Proof.
move=>hUnit x.
rewrite /compact_vector_open_extension; case:pselect=>[h|h]; first exact:hUnit.
have hNorm:=continuous_dual_norm_is_norm hD.
by rewrite (real_seminorm_zero hNorm.1) ler01.
Qed.
End OpenSubspaceWeakDualExtension.
