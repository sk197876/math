(** Federer (1969), 3.1.11, p. 220:
    differentiating an inverse-valued field on its
    given open domain. Inverses are already present
    pointwise, so this supporting local rule needs
    no completeness of the normed algebra. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom AlgebraUP RealNormUP AlgebraInverseUP
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  NormAlgebraInverseBounds NormAlgebraInverseDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_inverse_field]:
    the inverse differential used in the
    class-k induction of Federer 3.1.11,
    p. 220, pulled back to a
    specified domain where both inverse identities
    already hold. The derivative is
    h to -Q(a) DP(a)(h) Q(a).
    No ambient openness of the algebra's
    invertible set is assumed or needed. *)
Theorem norm_differential_inverse_field (R : realType)
    (X : lmodType R) (A : algebra R)
    (NX : X->R) (N : A->R) (hNX : is_real_norm NX) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (U : X->Prop) (P Q : X->A) a (L : Hom X A) :
  (forall x, U x -> is_two_sided_algebra_inverse (P x) (Q x)) ->
  has_norm_differential NX N U P a L ->
  has_norm_differential NX N U Q a
    (hom_comp (algebra_inverse_linear_term (Q a)) L).
Proof.
move=> hInv hP.
have ha := norm_domain_interior_member hNX (norm_differential_interior hP).
pose I := algebra_inverse_linear_term (Q a).
have hIb : norm_bounded_linear N N I := algebra_inverse_linear_term_bounded hN hM (Q a).
constructor.
- exact: norm_differential_interior hP.
- exact: norm_bounded_linear_compose (norm_differential_bounded hP) hIb.
- move=> e he.
  have [F [hF [r [hr hinc]]]] := norm_differential_increment_bound hN hP.
  have [B [hB hI]] := hIb.
  pose C := N (Q a)+1.
  have hQa := real_seminorm_nonnegative hN.1 (Q a).
  have hC : 0<C by rewrite /C; lra.
  have hCv : N (Q a)<=C by rewrite /C; lra.
  pose K0 := 2*C^+3*F^+2.
  have htwo : 0<=(2 : R) by rewrite ler0n.
  have hC3 : 0<=C^+3 := exprn_ge0 3 (ltW hC).
  have hF2 : 0<=F^+2 := exprn_ge0 2 (ltW hF).
  have hK0 : 0<=K0 := mulr_ge0 (mulr_ge0 htwo hC3) hF2.
  pose K := K0+B+1.
  have hK : 0<K by rewrite /K; lra.
  pose p := e/K.
  have hp : 0<p by rewrite /p divr_gt0.
  have hden : 0<2*C*F by nra.
  have [d [hd hrem]] := norm_differential_remainder hP hp.
  exists (Num.min r (Num.min p (Num.min ((2*C*F)^-1) d))).
  split; first by rewrite !lt_min hr hp invr_gt0 hden hd.
  move=> h hah; rewrite !lt_min=>/andP [hhr /andP [hhp /andP [hhi hhd]]].
  pose delta := P (a+h)-P a.
  have hn := real_seminorm_nonnegative hNX.1 h.
  have hdelta0 := real_seminorm_nonnegative hN.1 delta.
  have hdelta : N delta<=F*NX h := hinc h hah hhr.
  have hsmall : 2*C*N delta<=1.
    have hu : 2*C*F*NX h<1.
      by move: hhi; rewrite -div1r ltr_pdivlMr // mulrC.
    have hc0 : 0<=2*C by nra.
    have hs := ler_wpM2l hc0 hdelta; nra.
  have hnew : is_two_sided_algebra_inverse (P a+delta) (Q (a+h)).
    by rewrite /delta addrC subrK; exact: hInv (a+h) hah.
  have hquad := norm_algebra_inverse_quadratic_bound hN hM
    (hInv a ha) hnew hC hCv hsmall.
  have hfirst : N (Q (a+h)-Q a-I delta)<=K0*(NX h*NX h).
    change (N (Q (a+h)-Q a- -alg_mul A (Q a) (alg_mul A delta (Q a)))<=K0*(NX h*NX h)).
    rewrite opprK; apply: le_trans hquad _.
    have hs := ler_pM hdelta0 hdelta0 hdelta hdelta.
    have hc3 : 0<=2*C^+3 := mulr_ge0 htwo hC3.
    have ht := ler_wpM2l hc3 hs.
    have heq : 2*C^+3*((F*NX h)*(F*NX h))=K0*(NX h*NX h) by rewrite /K0; ring.
    rewrite heq in ht; by rewrite expr2.
  have hsecond : N (I (delta-L h))<=B*(p*NX h).
    apply: le_trans (hI _) _; apply: (ler_wpM2l hB).
    exact: hrem h hah hhd.
  have heq : Q (a+h)-Q a-hom_comp I L h=
      (Q (a+h)-Q a-I delta)+I (delta-L h).
    have hIB : I (delta-L h)=I delta-I (L h) :=
      linearB (hom_as_linear I) delta (L h).
    by rewrite hom_compE hIB addrA subrK.
  rewrite heq; apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  apply: le_trans (lerD hfirst hsecond) _.
  have hs := ler_wpM2l hK0 (ler_wpM2r hn (ltW hhp)).
  have hcoef : p*K=e by rewrite /p divfK // gt_eqF.
  have hpn : 0<=p*NX h := mulr_ge0 (ltW hp) hn.
  rewrite /K in hcoef; nra.
Qed.
