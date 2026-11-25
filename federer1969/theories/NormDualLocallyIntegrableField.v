(** Federer (1969), 4.1.19, p. 377, using
    4.1.1, p. 346: a norm-measurable locally
    integrable coefficient field has the original weak
    dual integrability needed for distribution smoothing.
    Norm-to-weak continuity is the already proved law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP
  ContinuousDualNorm OpenFamilyTopologyUP OpenFamilyTopologyMathcomp
  WeakEvaluationTopologyUP NormOpenTopology NormDualWeakContinuity
  PartialFunctionBasic MeasurableFunctionUP LocallyIntegrableVectorFieldUP
  DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_dual_locally_integrable_field]:
    the bounded measurable forms in Federer
    4.1.19, p. 377, give distributions
    by the original weak-field theorem of 4.1.1,
    p. 346. This general adapter requires
    neither full-dual separability nor completeness. *)
Theorem norm_dual_locally_integrable_field
    (R : realType) (X Y YD : lmodType R)
    (NX : X -> R) (NY : Y -> R) (DN : YD -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hDN : is_real_norm DN)
    (ed : Hom YD (Hom Y R^o)) (hDual : is_continuous_dual hNY ed DN)
    (O : set (set YD)) (hO : is_weak_evaluation_topology (fun a y => ed a y) O)
    (mu : set X -> \bar R) (f : X -> YD) :
  @is_locally_integrable_vector_field R X YD NX DN hNX hDN mu f ->
  @is_locally_integrable_weak_dual_field R X Y NX hNX YD ed DN O hO mu f.
Proof.
move=> [hMeas hLocal].
have hWeak := @norm_dual_weak_continuous R Y NY hNY YD ed DN hDual O hO.
have hNorm : continuous_dual_norm_is_norm hDual=hDN by exact: Prop_irrelevance.
rewrite hNorm in hWeak.
constructor; last exact: hLocal.
constructor; first exact: measurable_function_domain hMeas.
move=> A hA.
have hOpen : @open (real_norm_metric_space hDN) A := hWeak A hA.
exact: (measurable_function_open_preimage hMeas hOpen).
Qed.
