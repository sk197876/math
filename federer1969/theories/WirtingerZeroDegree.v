(** Federer (1969), 1.8.2, p. 40: the zeroth exterior power
    is the unit and 0!=1. With literal simplicity from 1.6.1,
    the only simple degree-zero vector is the empty product. Thus
    the zeroth Wirtinger case is valid without treating the
    degree-zero supremum as an absolute-value norm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates SimpleVectors SimpleZeroDegree
  InnerProductUP InnerNorm InnerExteriorLowDegrees ExteriorNorm
  ComassUP ComassZeroDegree TwoFormPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Zero.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable phi : A_m V R^o 2.

(** Source for [two_form_zeroth_simple_pairing]: Federer 1.8.2,
    p. 40, the pairing in degree zero is 1=0! for the only
    literally simple degree-zero vector. *)
Lemma two_form_zeroth_simple_pairing (x : exterior_power V 0) : simple x ->
  pairing x (two_form_power h2 phi 0) = 1.
Proof.
move/(proj1 (simple_zero_iff x))=> ->.
by rewrite two_form_power_zero -empty_e_lambda pairing_tuple zero_formE.
Qed.

(** Source for [two_form_zeroth_simple_norm]: Federer 1.8.2,
    p. 40, the literal empty simple product has Euclidean norm one. *)
Lemma two_form_zeroth_simple_norm (x : exterior_power V 0) : simple x ->
  exterior_norm h2 hB x = 1.
Proof.
move/(proj1 (simple_zero_iff x))=> ->.
apply: inner_norm_value; first exact: ler01.
by rewrite expr1n exterior_inner_zeroth mul1r.
Qed.

(** Source for [two_form_zeroth_comass]: Federer 1.8.2,
    p. 40, the zeroth-power comass is 1=0!, using exactly
    the literal supremum specification rather than a degree-zero norm axiom. *)
Theorem two_form_zeroth_comass : is_comass h2 hB (two_form_power h2 phi 0) 1.
Proof. rewrite two_form_power_zero; exact: literal_zeroth_comass. Qed.
End Zero.
