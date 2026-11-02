(** Sealed existence of the uniform norm, Federer (1969), 2.5.19,
    p. 113, used in 2.6.6, p. 120. Only the least-bound laws
    are exposed. Source conventions: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP UniformFunctionNormUP UniformFunctionNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type UniformFunctionNormSignature.
(** Source for [value]: the uniform norm of Federer 2.5.19, p. 113.
    Values outside K(X) are immaterial. *)
Parameter value : forall (R : realType) (X : topologicalType), (X -> R) -> R.
(** Source for [laws]: the defining least-bound laws of nu, Federer
    2.5.19, p. 113, supporting 2.6.6, p. 120. *)
Parameter laws : forall (R : realType) (X : topologicalType) (f : X -> R),
  compactly_supported_continuous_functions f -> is_uniform_function_norm f (@value R X f).
End UniformFunctionNormSignature.
Module UniformFunctionNorm : UniformFunctionNormSignature.
(** Source for [value]: private choice of the proved norm witness,
    Federer 2.5.19, p. 113. *)
Definition value (R : realType) (X : topologicalType) (f : X -> R) : R :=
  if pselect (compactly_supported_continuous_functions f) is left hf
  then sval (cid (compact_support_uniform_norm_exists hf)) else 0%R.
(** Source for [laws]: the chosen witness satisfies the abstract
    uniform-norm specification, Federer 2.5.19, p. 113. *)
Lemma laws (R : realType) (X : topologicalType) (f : X -> R) :
  compactly_supported_continuous_functions f -> is_uniform_function_norm f (value f).
Proof.
move=> hf; rewrite /value; case: pselect=> [h|hn]; last exact: False_ind (hn hf).
exact: svalP (cid (compact_support_uniform_norm_exists h)).
Qed.
End UniformFunctionNorm.
