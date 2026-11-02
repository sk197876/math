(** Federer (1969), 3.1.11, p. 220:
    continuity of an inverse-valued field on its
    given open domain. The nearby inverse is
    supplied by the field, so completeness is unnecessary. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import AlgebraUP RealNormUP AlgebraInverseUP NormClassOneUP
  NormAlgebraInverseContinuityBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_inverse_field]:
    the continuous inverse estimate supporting the
    higher inverse calculus in Federer 3.1.11,
    p. 220. Only pointwise inverse
    identities on the stated domain are used. *)
Theorem norm_class_zero_inverse_field (R : realType)
    (X : lmodType R) (A : algebra R)
    (NX : X->R) (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (U : X->Prop) (P Q : X->A) :
  (forall x, U x -> is_two_sided_algebra_inverse (P x) (Q x)) ->
  norm_class_zero NX N U P -> norm_class_zero NX N U Q.
Proof.
move=> hInv hP a ha; split; first exact: (hP a ha).1.
move=> e he.
pose C := N (Q a)+1.
have hQa := real_seminorm_nonnegative hN.1 (Q a).
have hC : 0<C by rewrite /C; lra.
have hCv : N (Q a)<=C by rewrite /C; lra.
have h2C : 0<2*C by nra.
have hC2 : 0<C^+2 := exprn_gt0 2 hC.
have h2C2 : 0<2*C^+2 by nra.
pose p := Num.min ((2*C)^-1) (e/(2*C^+2)).
have hp : 0<p by rewrite /p lt_min invr_gt0 h2C divr_gt0.
have [d [hd hcont]] := (hP a ha).2 p hp.
exists d; split=> // h hah hh.
have hdelta := hcont h hah hh.
move: hdelta; rewrite /p lt_min=>/andP [hs heps].
have hsmall : 2*C*N (P (a+h)-P a)<=1.
  apply: ltW; by move: hs; rewrite -div1r ltr_pdivlMr // mulrC.
have hnew : is_two_sided_algebra_inverse
    (P a+(P (a+h)-P a)) (Q (a+h)).
  by rewrite addrC subrK; exact: hInv (a+h) hah.
apply: le_lt_trans (norm_algebra_inverse_difference_bound hN hM
  (hInv a ha) hnew hC hCv hsmall) _.
by move: heps; rewrite ltr_pdivlMr // mulrC.
Qed.
