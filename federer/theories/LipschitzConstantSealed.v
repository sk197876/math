(** Federer (1969), 2.2.7, p. 64: sealed least Lipschitz
    constant. Editions and zero-bound convention: LipschitzUP.v.
    The real-infimum witness is hidden by opaque module ascription. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import LipschitzUP LipschitzConstantConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type LipschitzConstantSignature.
(** Source for [value]: Federer 2.2.7, p. 64, the least
    finite Lipschitz constant of a Lipschitzian map. *)
Parameter value : forall (R : realType) (T U : metricType R)
  (X : set T) (f : T -> U), is_metric_lipschitz X f -> R.
(** Source for [laws]: Federer 2.2.7, p. 64, abstract
    attainment and minimality of Lip(f). *)
Parameter laws : forall (R : realType) (T U : metricType R)
  (X : set T) (f : T -> U) (h : is_metric_lipschitz X f),
  is_least_metric_lipschitz_constant X f (@value R T U X f h).
End LipschitzConstantSignature.
Module LipschitzConstant : LipschitzConstantSignature.
(** Source for [value]: supporting witness selection for Federer
    2.2.7, p. 64, from the proved least-constant existence theorem. *)
Definition value (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) :=
  projT1 (cid (least_metric_lipschitz_constant_exists h)).
(** Source for [laws]: Federer 2.2.7, p. 64, the selected
    witness satisfies the least-constant specification. *)
Lemma laws (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (h : is_metric_lipschitz X f) :
  is_least_metric_lipschitz_constant X f (@value R T U X f h).
Proof. exact: projT2 (cid (least_metric_lipschitz_constant_exists h)). Qed.
End LipschitzConstant.
