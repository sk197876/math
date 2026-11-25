(** Federer (1969), 4.1.19, p. 377: the
    actual coefficient convolution may be evaluated on
    every fixed multivector. The earlier continuous-dual
    and vector-integral laws retain every natural degree. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  GrassmannAbbreviations ExteriorGrading AlternatingForms AlternatingPairing
  PairingLinear CurrentCoefficientNorms CurrentMultivectorDual
  MultivectorDualSealed ContinuousDualUP PartialFunctionUP PartialFunctionBasic
  MeasureVectorIntegralUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_form_integral_pairing]: the
    actual scalar evaluation of Phi_epsilon*phi in
    Federer 4.1.19, p. 377. This
    supporting law follows directly from the original
    vector integral, with no positivity assumption. *)
Theorem current_form_integral_pairing (R : realType) (h2 : (1+1:R)!=0)
    n m (B : choiceType) (mu : set B -> \bar R)
    (F : B -> A_m (R_n R n) R^o m)
    (y : A_m (R_n R n) R^o m)
    (theta : exterior_power (R_n R n) m) :
  is_measure_vector_integral mu (partial_function_total
    (fun x => (F x : real_norm_metric_space
      (@current_form_comass_real_norm R h2 n m)))) y ->
  is_measure_integral mu (real_total_integrand (fun x => pairing theta (F x)))
    (pairing theta y)%:E.
Proof.
move=> hIntegral.
pose L := @MultivectorDual.evaluation R (R_n R n) m theta.
have hContinuous := @continuous_dual_continuous R (A_m (R_n R n) R^o m)
  (@current_form_comass R h2 n m) (@current_form_comass_real_norm R h2 n m)
  (exterior_power (R_n R n) m) (@MultivectorDual.evaluation R (R_n R n) m)
  (@current_vector_mass R h2 n m) (@current_multivector_continuous_dual R h2 n m) theta.
have hScalar := hIntegral.2 (hom_as_linear L) hContinuous.
have hValue : L y=pairing theta y.
  exact: (@MultivectorDual.laws R (R_n R n) m theta y).
rewrite hom_as_linearE hValue in hScalar.
apply: (@measure_integral_graph_equivalent R B mu _ _ _ _ hScalar)=> x a.
split.
- move=> [v [hv ha]]; apply/real_total_integrand_graph.
  change (F x=v) in hv.
  by rewrite hv -(@MultivectorDual.laws R (R_n R n) m theta v).
- move/real_total_integrand_graph=> ha.
  exists (F x); split; first reflexivity.
  by rewrite hom_as_linearE (@MultivectorDual.laws R (R_n R n) m theta (F x)).
Qed.
