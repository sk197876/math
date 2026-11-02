(** Opaque elementary scalar functions for Federer (1969), 2.4.12–13, pp.
    86–88. Source context and dependency rationale: RealExponentialUP.v and
    RealExponentialConstruction.v. *)
From mathcomp Require Import all_boot boolp reals.
From Federer Require Import RealExponentialUP RealExponentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type RealExponentialSignature.
(** Source for [exponential]: elementary exponential used in
    Federer 2.4.13, p. 88, exposed abstractly. *)
Parameter exponential : forall R : realType, R -> R.
(** Source for [logarithm]: elementary logarithm used in
    Federer 2.4.13, p. 88, exposed abstractly. *)
Parameter logarithm : forall R : realType, R -> R.
(** Source for [laws]: defining scalar laws supporting
    Federer 2.4.12–13, pp. 86–88. *)
Parameter laws : forall R : realType,
  is_real_exponential_logarithm (@exponential R) (@logarithm R).
End RealExponentialSignature.
Module RealExponential : RealExponentialSignature.
(** Source for [exponential]: selected scalar exponential for
    Federer 2.4.13, p. 88. *)
Definition exponential (R : realType) := projT1 (cid (@real_exponential_logarithm_exists R)).
(** Source for [logarithm]: selected inverse logarithm for
    Federer 2.4.13, p. 88. *)
Definition logarithm (R : realType) :=
  projT1 (cid (projT2 (cid (@real_exponential_logarithm_exists R)))).
(** Source for [laws]: proof that the selected functions satisfy
    the scalar laws supporting Federer 2.4.12–13, pp. 86–88. *)
Lemma laws (R : realType) :
  is_real_exponential_logarithm (@exponential R) (@logarithm R).
Proof. exact: projT2 (cid (projT2 (cid (@real_exponential_logarithm_exists R)))). Qed.
End RealExponential.
