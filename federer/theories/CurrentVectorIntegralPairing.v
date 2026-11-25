(** Federer (1969), 4.1.18, pp. 375–376: every
    original fixed covector may evaluate the ordinary
    multivector convolution integral. Its boundedness
    follows from the already proved finite exterior
    basis, without any new dual-space hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormFiniteLinearBound
  NormBoundedLinearTopology ScalarNormExtendedEmbedding GrassmannAbbreviations ExteriorGrading
  AlternatingForms AlternatingDual AlternatingIsomorphism AlternatingPairing CurrentCoefficientNorms CurrentVectorSpaces
  ContinuousRealFunctional PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_vector_integral_pairing]: scalar
    evaluations of the actual ordinary field convolution,
    supporting the first proposition of Federer 4.1.18,
    p. 375, by the original vector-integral definition
    of 2.4.12, p. 87. *)
Theorem current_vector_integral_pairing (R:realType) (h2:(1+1:R)!=0)
    n m (B:choiceType) (mu:set B->\bar R)
    (F:B->exterior_power (R_n R n) m) (y:exterior_power (R_n R n) m)
    (theta:A_m (R_n R n) R^o m):
  is_measure_vector_integral mu (partial_function_total
    (fun x=>(F x:real_norm_metric_space (@current_vector_mass_real_norm R h2 n m)))) y ->
  is_measure_integral mu (real_total_integrand (fun x=>pairing (F x) theta))
    (pairing y theta)%:E.
Proof.
move=>hI.
pose V:=exterior_power (R_n R n) m.
pose VN:=@current_vector_mass R h2 n m.
pose hVN:=@current_vector_mass_real_norm R h2 n m.
pose L:Hom V R^o:=form_to_hom theta.
have[k [b hb]]:=@current_vector_finite_basis R h2 n m.
have [C [hC hBound]]:=@norm_finite_linear_bounded R V R^o VN (fun t:R^o=>`|t|)
  hVN (@scalar_absolute_value_norm R) k b hb L.
have hContinuous:is_continuous_real_functional hVN (hom_as_linear L).
  exact:(@bounded_real_functional_continuous R V VN hVN
    (hom_as_linear L) C hC hBound).
have hScalar:=hI.2 (hom_as_linear L) hContinuous.
apply:(@measure_integral_graph_equivalent R B mu _ _ _ _ hScalar)=>x a.
split.
- move=>[v [hv ha]];apply/real_total_integrand_graph.
  change (F x=v) in hv;by rewrite hv.
- move/real_total_integrand_graph=>ha.
  exists (F x);split;first reflexivity.
  exact:ha.
Qed.
