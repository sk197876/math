(** Federer (1969), 4.1.7, p. 358:
    an arbitrary measurable multivector density
    has measurable mass norm. The actual
    finite weak-to-norm identity and the
    existing norm-continuity theorem prove this
    without a bounded-density hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealNormUP NormMetric NormMetricContinuity OpenFamilyTopologyUP OpenFamilyTopologyMathcomp
  GrassmannAbbreviations ExteriorGrading CurrentCoefficientNorms CurrentMultivectorDual CurrentWeakNormTopology
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableTotalBasic MeasureStepIntegralIdentification
  BorelFunctionBasic SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_density_mass_topology_measurable]:
    an original weakly measurable multivector field
    is measurable in its actual mass-norm topology,
    supporting Federer 4.1.7, pp. 357–358.
    Only the proved finite-dimensional topology map
    is used. *)
Theorem current_density_mass_topology_measurable (R:realType) (h2:(1+1:R)!=0) n m (B:choiceType)
    (gamma:set B->\bar R) (hm:is_measure gamma) (xi:B->exterior_power (R_n R n) m):
  is_measure_measurable_function gamma
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))) ->
  is_measure_measurable_function gamma (partial_function_total
    (fun x=>(xi x:real_norm_metric_space (@current_vector_mass_real_norm R h2 n m)))).
Proof.
move=>hXi.
pose W:=open_family_topological_space (@current_multivector_weak_laws R n m).1.
pose V:=real_norm_metric_space (@current_vector_mass_real_norm R h2 n m).
have hId:continuous (fun z:W=>(z:V)).
  rewrite continuousP; exact:(@current_weak_mass_norm_continuous R h2 n m).
exact:(@measurable_total_borel_postcomposition R B W V gamma hm
  (fun x=>(xi x:W)) (fun z=>(z:V)) hXi (continuous_borel_function hId)).
Qed.

(** Source for [current_density_weak_topology_measurable]:
    mass-norm measurable multivector fields are
    measurable in the original weak topology,
    supporting Federer 4.1.7, pp. 357–358.
    This is the reverse actual topology adapter. *)
Theorem current_density_weak_topology_measurable (R:realType) (h2:(1+1:R)!=0) n m (B:choiceType)
    (gamma:set B->\bar R) (hm:is_measure gamma) (xi:B->exterior_power (R_n R n) m):
  is_measure_measurable_function gamma (partial_function_total
    (fun x=>(xi x:real_norm_metric_space (@current_vector_mass_real_norm R h2 n m)))) ->
  is_measure_measurable_function gamma
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))).
Proof.
move=>hXi.
pose W:=open_family_topological_space (@current_multivector_weak_laws R n m).1.
pose V:=real_norm_metric_space (@current_vector_mass_real_norm R h2 n m).
have hId:continuous (fun z:V=>(z:W)).
  rewrite continuousP; exact:(@current_mass_norm_weak_continuous R h2 n m).
exact:(@measurable_total_borel_postcomposition R B V W gamma hm
  (fun x=>(xi x:V)) (fun z=>(z:W)) hXi (continuous_borel_function hId)).
Qed.

(** Source for [current_density_mass_measurable]: the
    mass norm in gamma restricted by
    mass(xi) is measurable for every
    original weakly measurable multivector field,
    supporting Federer 4.1.7, p. 358. *)
Theorem current_density_mass_measurable (R:realType) (h2:(1+1:R)!=0) n m (B:choiceType)
    (gamma:set B->\bar R) (hm:is_measure gamma) (xi:B->exterior_power (R_n R n) m):
  is_measure_measurable_function gamma
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))) ->
  is_measure_measurable_function gamma (real_total_integrand
    (fun x=>@current_vector_mass R h2 n m (xi x))).
Proof.
move=>hXi.
pose D:=exterior_power (R_n R n) m.
pose N:=@current_vector_mass R h2 n m.
pose hN:=@current_vector_mass_real_norm R h2 n m.
pose O:=@current_multivector_weak_opens R n m.
pose hO:=@current_multivector_weak_laws R n m.
pose W:=open_family_topological_space hO.1.
have hId:continuous (fun d:W=>(d:real_norm_metric_space hN)).
  rewrite continuousP;exact:(@current_weak_mass_norm_continuous R h2 n m).
have hNorm:continuous (fun d:W=>(N d:real_line_metric R)).
  move=>d;exact:(continuous_comp (hId d) (@real_norm_metric_norm_continuous R D N hN d)).
have hReal:=@measurable_total_borel_postcomposition R B W (real_line_metric R) gamma hm
  (fun x=>(xi x:W)) (fun d=>N d) hXi (continuous_borel_function hNorm).
exact:(@measurable_partial_real_embedding R B gamma hm
  (partial_function_total (fun x=>(N (xi x):real_line_metric R))) hReal).
Qed.
