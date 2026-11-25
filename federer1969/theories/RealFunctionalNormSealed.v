(** Sealed dual-norm existence for Federer (1969), 2.4.12, p. 87. Source
    context and the equivalent least-bound specification are recorded in
    RealFunctionalNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP ContinuousRealFunctional
  RealFunctionalNormUP RealFunctionalNormConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RealFunctionalNormSignature.
(** Source for [value]: the finite dual norm of a continuous real
    linear functional, Federer 2.4.12, p. 87. *)
Parameter value : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}),
  is_continuous_real_functional hN a -> R.
(** Source for [laws]: the least-bound laws of the dual norm,
    Federer 2.4.12, p. 87. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o})
  (ha : is_continuous_real_functional hN a),
  is_real_functional_norm N a (@value R V N hN a ha).
End RealFunctionalNormSignature.

Module RealFunctionalNorm : RealFunctionalNormSignature.
(** Source for [value]: private witness of the dual norm in
    Federer 2.4.12, p. 87, from its proved existence. *)
Definition value (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o})
  (ha : is_continuous_real_functional hN a) : R :=
  projT1 (cid (real_functional_norm_exists ha)).
(** Source for [laws]: the chosen dual norm satisfies its
    abstract specification, Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o})
  (ha : is_continuous_real_functional hN a) :
  is_real_functional_norm N a (value ha).
Proof. exact: projT2 (cid (real_functional_norm_exists ha)). Qed.
End RealFunctionalNorm.
