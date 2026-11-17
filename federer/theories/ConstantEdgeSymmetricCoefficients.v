(** Supporting Federer (1969), 3.2.36, p. 273, and 3.2.45,
    p. 280: the elementary symmetric coefficients of equal cube edges. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ElementarySymmetricCoefficientsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [constant_edge_symmetric_coefficients]: supporting
    the cube coefficients in Federer 3.2.45, p. 280, from the
    elementary symmetric formula of 3.2.36, p. 273. The existing
    binomial theorem proves the independent coefficient laws for all
    real edge values, including zero, and dimension zero. *)
Lemma constant_edge_symmetric_coefficients (R : realType) n (s : R) :
  is_elementary_symmetric_coefficients (fun _ : 'I_n => s)
    (fun j : 'I_n.+1 => 'C(n,j)%:R * s^+j).
Proof.
move=> t.
rewrite prodr_const card_ord exprDn.
apply: eq_bigr=> j _.
by rewrite expr1n mul1r exprMn -mulr_natl mulrA.
Qed.
