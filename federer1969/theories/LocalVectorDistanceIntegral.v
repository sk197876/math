(** Federer (1969), 4.1.2, p. 347: the
    local smoothing error has a finite actual norm
    integral on each compact ball. The argument
    reuses the integrated distance triangle inequality
    of 2.9.9, pp. 156–157. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral SummableRealFunctionUP
  MeasurableDistanceTo DistanceSubsetIntegral BoundedVectorDistanceSubsetIntegral SmoothCompactSet LocallyIntegrableVectorFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [total_norm_distance_subset_graph]: the norm-error
    integral in Federer 4.1.2, p. 347,
    with the original subset-integral convention of 2.4.10, p. 85. *)
Lemma total_norm_distance_subset_graph (R:realType) (X:Type) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (A:set X) (f:X->Y) (a:Y) x z:
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (partial_distance_to (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) a)) x z <->
  partial_function_graph (real_total_integrand (fun x=>if pselect (A x) then NY (f x-a) else 0)) x z.
Proof.
rewrite real_total_integrand_graph.
case:(pselect (A x))=>hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx) total_norm_distance_graph.
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (z=(0:extended_real_line R)<->(0:extended_real_line R)=z).
  split=>->; reflexivity.
Qed.

(** Source for [locally_integrable_vector_compact_distance]: local
    norm integrability gives the actual finite distance
    integral at every fixed target value, supporting
    Federer 4.1.2, p. 347. The compact
    set has only its original finite measurable mass. *)
Theorem locally_integrable_vector_compact_distance (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y)
    (K:smooth_compact_set hNX (fun _=>True)) (m:R) (a:Y):
  @is_locally_integrable_vector_field R X Y NX NY hNX hNY mu f ->
  measure_measurable mu (smooth_compact_carrier K) ->mu (smooth_compact_carrier K)=m%:E ->
  exists J:R,is_measure_subset_integral mu (smooth_compact_carrier K)
    (partial_distance_to (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) a) J%:E.
Proof.
move=>hField hK hMass.
have [b hNorm]:=@locally_integrable_vector_compact_norm R X Y NX NY hNX hNY mu f hField K.
have hBase:is_measure_subset_integral mu (smooth_compact_carrier K)
    (partial_distance_to (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) 0) b%:E.
  apply:(measure_integral_graph_equivalent _ hNorm)=>x z.
  have hGraph:=@total_norm_distance_subset_graph R X Y NY hNY (smooth_compact_carrier K) f 0 x z.
  rewrite real_total_integrand_graph.
  rewrite real_total_integrand_graph subr0 in hGraph; symmetry; exact hGraph.
have [J [hJ _]]:=@distance_subset_integral_bound R X (real_norm_metric_space hNY)
  mu (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))) (smooth_compact_carrier K) b m 0 a
  hm (@locally_integrable_vector_measurable R X Y NX NY hNX hNY mu f hField) hK hMass hBase.
exists J; exact hJ.
Qed.
