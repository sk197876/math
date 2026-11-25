(** Federer (1969), 1.6.6, p. 26: the inclusion of complex multilinear forms
    preserves their alternating products. The proof compares the shuffle
    formula of 1.4.2, p. 18, over the two fields. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import ScalarRestriction ComplexAlternatingForms
  AlternatingForms AlternatingProduct AlternatingShuffle InversionCount TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Restriction.
Variables R C : fieldType.
Hypothesis hR : (1+1 : R) != 0.
Hypothesis hC : (1+1 : C) != 0.
Variable embed : {rmorphism R -> C}.
Variables V W : lmodType C.
Local Notation VR := (restricted_space embed V).
Local Notation WR := (restricted_space embed W).
Variable mu : W -> W -> W.
Hypothesis hc : bilinear mu.
Hypothesis hr : @bilinear R WR WR WR mu.

(** Source for [restriction_permutation_sign]: Federer 1.6.6,
    p. 26, complex subalgebra assertion. Supporting fact: the shuffle
    signs of 1.4.2, p. 18, are preserved by the scalar embedding. *)
Lemma restriction_permutation_sign n (s : 'S_n) :
  embed (FedererPermutation.index R s) = FedererPermutation.index C s.
Proof. by rewrite /FedererPermutation.index rmorphXn rmorphN rmorph1. Qed.

(** Source for [restrict_form_wedge]: Federer 1.6.6, p. 26,
    complex subalgebra assertion. The alternating product over the
    complex field agrees with the product of the underlying real forms.
    This supporting statement allows any field embedding and any common
    coefficient multiplication with the displayed bilinearity laws. *)
Theorem restrict_form_wedge p q (a : A_m V W p) (b : A_m V W q) :
  restrict_form embed (form_wedge hC hc a b) =
  form_wedge hR hr (restrict_form embed a) (restrict_form embed b).
Proof.
apply: form_ext => t.
change (form_wedge hC hc a b t =
  form_wedge hR hr (restrict_form embed a) (restrict_form embed b) t).
rewrite !form_wedge_shuffle.
apply: eq_bigr => s _.
have hl : @shuffle_left_tuple R VR p q t (val s) =
    @shuffle_left_tuple C V p q t (val s) by apply: val_inj.
have ht : @shuffle_right_tuple R VR p q t (val s) =
    @shuffle_right_tuple C V p q t (val s) by apply: val_inj.
rewrite hl ht.
change (FedererPermutation.index C (val s) *:
  mu (a (@shuffle_left_tuple C V p q t (val s))) (b (@shuffle_right_tuple C V p q t (val s))) =
  embed (FedererPermutation.index R (val s)) *:
  mu (a (@shuffle_left_tuple C V p q t (val s))) (b (@shuffle_right_tuple C V p q t (val s)))).
by rewrite restriction_permutation_sign.
Qed.
End Restriction.
