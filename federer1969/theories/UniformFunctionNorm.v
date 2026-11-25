(** Public uniform norm, Federer (1969), 2.5.19, p. 113, for the extension
    in 2.6.6, p. 120. This interface uses only the sealed least-bound
    specification; Source context: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP UniformFunctionNormUP UniformFunctionNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [compact_support_uniform_norm]: nu(f) in Federer
    2.5.19, p. 113. Its public laws concern f in K(X). *)
Definition compact_support_uniform_norm (R : realType) (X : topologicalType) (f : X -> R) :=
  @UniformFunctionNorm.value R X f.

(** Source for [compact_support_uniform_norm_specification]: the
    least-bound characterization of nu, Federer 2.5.19, p. 113. *)
Lemma compact_support_uniform_norm_specification (R : realType) (X : topologicalType) (f : X -> R) :
  compactly_supported_continuous_functions f ->
  is_uniform_function_norm f (compact_support_uniform_norm f).
Proof. exact: (@UniformFunctionNorm.laws R X f). Qed.
