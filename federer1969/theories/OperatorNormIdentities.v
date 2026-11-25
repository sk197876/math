(** Federer (1969), 1.7.6, p. 33: ||f|| = ||adjoint f|| = ||dual f|| for
    finite-dimensional inner-product spaces. These public formulas
    instantiate the abstract norm identities with the sealed operator norm
    and the original dual metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerDual LinearBasis TraceDual
  AlternatingCoordinates Adjoint AdjointUP OperatorNormUP OperatorNorm
  OperatorNormAdjoint OperatorDualNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Identities.
Variable R : realType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variables n k : nat.
Variable b : 'I_n -> V.
Variable e : 'I_k -> U.
Hypothesis hb : is_basis b.
Hypothesis he : is_basis e.
Variable f : {linear V -> U}.

(** Source for [linear_operator_adjoint_norm_equal]: Federer
    1.7.6, p. 33, the chosen adjoint has the same operator norm
    as f, with any finite source and target bases. *)
Theorem linear_operator_adjoint_norm_equal :
  linear_operator_norm hB hC hb f =
    linear_operator_norm hC hB he (inner_adjoint hB hC hb f).
Proof.
exact (@operator_norm_adjoint_equal R V U B C hB hC f
  (inner_adjoint hB hC hb f) _ _ (inner_adjointP hB hC hb f)
  (linear_operator_normP hB hC hb f)
  (linear_operator_normP hC hB he (inner_adjoint hB hC hb f))).
Qed.

(** Source for [dual_linear_operator_norm]: Federer 1.7.6,
    p. 33, the norm of the degree-one dual map, computed with
    the dual inner products defined in 1.7.2. *)
Definition dual_linear_operator_norm := linear_operator_norm
  (inner_dual_productP hC he) (inner_dual_productP hB hb)
  (one_covector_basisP he) (form_pullback_linear f 1).

(** Source for [dual_linear_operator_normP]: Federer 1.7.6,
    p. 33, the degree-one dual norm satisfies the operator norm laws. *)
Theorem dual_linear_operator_normP :
  is_operator_norm (inner_dual_productP hC he) (inner_dual_productP hB hb)
    (form_pullback_linear f 1) dual_linear_operator_norm.
Proof. exact: linear_operator_normP. Qed.

(** Source for [linear_operator_dual_norm_equal]: Federer
    1.7.6, p. 33, equality of the norms of f and its degree-one dual. *)
Theorem linear_operator_dual_norm_equal :
  linear_operator_norm hB hC hb f = dual_linear_operator_norm.
Proof.
exact (@operator_dual_norm_equal R V U B C hB hC n k b e hb he f
  (inner_adjoint hB hC hb f) (inner_adjointP hB hC hb f)
  _ (linear_operator_norm hC hB he (inner_adjoint hB hC hb f)) _
  (linear_operator_normP hB hC hb f)
  (linear_operator_normP hC hB he (inner_adjoint hB hC hb f))
  dual_linear_operator_normP).
Qed.
End Identities.
