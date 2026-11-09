(** Federer (1969), 3.4.6, p. 322: scalar
    normalization transports actual division equations without
    changing the original direction or the remainder condition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRing WeierstrassDivisionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_division_from_normalization]:
    absorbing the normalizing scalar in Q restores the
    original phi and preserves the actual remainder,
    supporting 3.4.6(1), p. 322. *)
Lemma weierstrass_division_from_normalization (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) k (v:X)
    (C Phi Psi Q T:@analytic_germ_ring R X NX hNX 0):
  @is_weierstrass_division R X NX hNX k v (C*Phi) Psi Q T ->
  @is_weierstrass_division R X NX hNX k v Phi Psi (Q*C) T.
Proof.
move=>hDivision;constructor.
- by rewrite -mulrA -(weierstrass_division_identity hDivision).
- exact:weierstrass_division_polynomial_remainder hDivision.
Qed.

(** Source for [weierstrass_division_to_normalization]:
    the inverse scalar sends every original division
    candidate to a normalized one, supporting the germ
    uniqueness assertion of 3.4.6(1), p. 322. *)
Lemma weierstrass_division_to_normalization (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) k (v:X)
    (C D Phi Psi Q T:@analytic_germ_ring R X NX hNX 0):
  D*C= 1 ->@is_weierstrass_division R X NX hNX k v Phi Psi Q T ->
  @is_weierstrass_division R X NX hNX k v (C*Phi) Psi (Q*D) T.
Proof.
move=>hInverse hDivision;constructor.
- have hProduct:(Q*D)*(C*Phi)=Q*Phi.
    by rewrite mulrA -[Q*D*C]mulrA hInverse mulr1.
  by rewrite hProduct -(weierstrass_division_identity hDivision).
- exact:weierstrass_division_polynomial_remainder hDivision.
Qed.
