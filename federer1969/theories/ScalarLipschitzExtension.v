(** Public scalar extension supporting Federer (1969), 2.5.9, p. 100. The
    extension is specified by agreement and a unit Lipschitz bound. Source
    context: ScalarLipschitzExtensionUP.v. No downstream result needs the
    infimum implementation. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import ScalarLipschitzExtensionUP ScalarLipschitzExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [scalar_lipschitz_extension]: public witness for
    the continuous extension in Federer 2.5.9, p. 100. *)
Definition scalar_lipschitz_extension (R : realType) (T : Type) (W D : set T)
    (d : T -> T -> R) (A : T -> R) (hd : is_pseudometric_on_set W d)
    (hDW : (forall x, D x -> W x)) (hD : exists y, D y) (hA : is_scalar_lipschitz_on_set D d A) :=
  @ScalarLipschitzExtension.value R T W D d A hd hDW hD hA.

(** Source for [scalar_lipschitz_extension_specification]:
    agreement and continuity supporting Federer 2.5.9, p. 100. *)
Lemma scalar_lipschitz_extension_specification (R : realType) (T : Type) (W D : set T)
    (d : T -> T -> R) (A : T -> R) (hd : is_pseudometric_on_set W d)
    (hDW : (forall x, D x -> W x)) (hD : exists y, D y) (hA : is_scalar_lipschitz_on_set D d A) :
  is_scalar_lipschitz_extension W D d A (@scalar_lipschitz_extension R T W D d A hd hDW hD hA).
Proof. exact: (@ScalarLipschitzExtension.laws R T W D d A hd hDW hD hA). Qed.
