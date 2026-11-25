(** Federer (1969), 1.7.3, p. 29: supporting evaluation of the finite sum in
    the alternating two-form normal form. The evaluation laws hold for forms
    of any degree and any coefficient module. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Evaluation.
Variable R : fieldType.
Variables V W : lmodType R.
Variable m : nat.
Variable t : m.-tuple V.

(** Source for [form_evaluate]: Federer 1.7.3, p. 29,
    supporting evaluation of the proposed sum of wedge products. *)
Definition form_evaluate (phi : A_m V W m) := phi t.

(** Source for [form_evaluate_linear]: Federer 1.7.3,
    p. 29, evaluation respects addition and scalar multiplication
    when checking the displayed normal-form equality. *)
Lemma form_evaluate_linear : linear form_evaluate.
Proof. by move=> a phi psi; rewrite /form_evaluate form_addE form_scaleE. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (A_m V W m) W *:%R
  form_evaluate form_evaluate_linear.
End Evaluation.
