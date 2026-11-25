(** Sealed scalar extension for the continuous-extension step in Federer
    (1969), 2.5.9, p. 100. Source context and the distinction between the
    book's proof and the chosen witness construction are recorded in
    ScalarLipschitzExtensionConstruction.v. Downstream proofs use only
    agreement and Lipschitz continuity. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import ScalarLipschitzExtensionUP ScalarLipschitzExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type ScalarLipschitzExtensionSignature.
(** Source for [value]: abstract extension supporting Federer
    2.5.9, p. 100; no implementation is exposed. *)
Parameter value : forall (R : realType) (T : Type) (W D : set T)
  (d : T -> T -> R) (A : T -> R), is_pseudometric_on_set W d ->
  (forall x, D x -> W x) -> (exists y, D y) -> is_scalar_lipschitz_on_set D d A -> T -> R.
(** Source for [laws]: agreement and continuity of the extension
    supporting Federer 2.5.9, p. 100. *)
Parameter laws : forall (R : realType) (T : Type) (W D : set T)
  (d : T -> T -> R) (A : T -> R) (hd : is_pseudometric_on_set W d)
  (hDW : (forall x, D x -> W x)) (hD : exists y, D y) (hA : is_scalar_lipschitz_on_set D d A),
  is_scalar_lipschitz_extension W D d A (@value R T W D d A hd hDW hD hA).
End ScalarLipschitzExtensionSignature.
Module ScalarLipschitzExtension : ScalarLipschitzExtensionSignature.
(** Source for [value]: private witness selection for the extension
    in Federer 2.5.9, p. 100; existence was proved separately. *)
Definition value (R : realType) (T : Type) (W D : set T)
    (d : T -> T -> R) (A : T -> R) (hd : is_pseudometric_on_set W d)
    (hDW : (forall x, D x -> W x)) (hD : exists y, D y) (hA : is_scalar_lipschitz_on_set D d A) :=
  projT1 (cid (@scalar_lipschitz_extension_exists R T W D d A hd hDW hD hA)).
(** Source for [laws]: verified extension laws supporting Federer
    2.5.9, p. 100. *)
Lemma laws (R : realType) (T : Type) (W D : set T)
    (d : T -> T -> R) (A : T -> R) (hd : is_pseudometric_on_set W d)
    (hDW : (forall x, D x -> W x)) (hD : exists y, D y) (hA : is_scalar_lipschitz_on_set D d A) :
  is_scalar_lipschitz_extension W D d A (@value R T W D d A hd hDW hD hA).
Proof. exact: projT2 (cid (@scalar_lipschitz_extension_exists R T W D d A hd hDW hD hA)). Qed.
End ScalarLipschitzExtension.
