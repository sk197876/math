(** Federer (1969), 3.2.16, p. 253:
    differentiability relative to the agreement set.
    Keep the standing domain of the relative
    definition in 3.1.22, p. 235: a lies
    in its closure. No positive density premise
    is inserted into approximate differentiability. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialFunctionExtensionUP TangentConeUP RelativeDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [differentiable_representative_relative_agreement]:
    the relative differentiability assertion after
    the definition in Federer 3.2.16, p. 253,
    with the closure-domain convention of 3.1.22,
    p. 235. This proof uses actual agreement
    values and any graph-preserving total representative. *)
Theorem differentiable_representative_relative_agreement (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (f : partial_function X Y)
    (U : set X) (g f0 : X -> Y) a (D : Hom X Y) :
  is_partial_function_total_extension f f0 ->
  has_norm_differential NX NY U g a D ->
  @closure (real_norm_metric_space hNX)
    (partial_function_agreement f (partial_function_source_restrict U (partial_function_total g))) a ->
  @relative_norm_differentiable_at R X Y NX NY hNX (partial_function_domain f)
    (partial_function_agreement f (partial_function_source_restrict U (partial_function_total g))) f0 a.
Proof.
move=> hExt hg hcl.
pose S := partial_function_agreement f (partial_function_source_restrict U (partial_function_total g)).
exists (partial_function_source_restrict (norm_tangent_cone NX S a) (partial_function_total D)).
split; first exact hcl.
exists U,g,D; split=> //; split.
- move=> x [y [hfy [_ hgy]]] _; split; first by exists y.
  exact: eq_trans (hExt x y hfy) (esym hgy).
- by move=> v y.
Qed.
