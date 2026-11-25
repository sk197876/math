(** Federer (1969), 4.1.18, p. 374: every
    original multivector pairing commutes with the
    actual vector integral of form values. Reuse
    the exact mass/comass continuous duality of 4.1.7,
    without adding target separability.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP
  PartialFunctionBasic MeasureVectorIntegralUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_form_vector_integral_pairing]:
    scalarise the literal original smoothing integral
    by every eta, supporting 4.1.18, p. 374,
    through the original integral definition of 2.4.12,
    p. 87, and duality of 4.1.7, p. 357. *)
Theorem current_form_vector_integral_pairing (R:realType) (h2:(1+1:R)!=0)
    n j (B:choiceType) (mu:set B->\bar R)
    (F:B->A_m (R_n R n) R^o j) (y:A_m (R_n R n) R^o j)
    (eta:exterior_power (R_n R n) j):
  is_measure_vector_integral mu (partial_function_total
    (fun z=>(F z:real_norm_metric_space (@current_form_comass_real_norm R h2 n j)))) y ->
  is_measure_integral mu (real_total_integrand (fun z=>pairing eta (F z)))
    (pairing eta y)%:E.
Proof.
move=>hIntegral.
pose ev:=@MultivectorDual.evaluation R (R_n R n) j.
pose hDual:=@current_multivector_continuous_dual R h2 n j.
have hScalar:=hIntegral.2 (hom_as_linear (ev eta)) (@continuous_dual_continuous R (A_m (R_n R n) R^o j)
  (@current_form_comass R h2 n j) (@current_form_comass_real_norm R h2 n j)
  (exterior_power (R_n R n) j) ev (@current_vector_mass R h2 n j) hDual eta).
rewrite hom_as_linearE /ev (@MultivectorDual.laws R (R_n R n) j eta y) in hScalar.
apply:(@measure_integral_graph_equivalent R B mu _ _ _ _ hScalar)=>z a.
split.
- move=>[v [hv hValue]];apply/real_total_integrand_graph.
  change (F z=v) in hv.
  change ((ev eta v)%:E=a) in hValue.
  by rewrite hv -(@MultivectorDual.laws R (R_n R n) j eta v).
- move/real_total_integrand_graph=>hValue.
  exists (F z);split;first reflexivity.
  change ((ev eta (F z))%:E=a).
  by rewrite MultivectorDual.laws.
Qed.
