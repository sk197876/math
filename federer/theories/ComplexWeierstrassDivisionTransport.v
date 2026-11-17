(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, p. 322: scalar
    normalization transports actual division equations without
    changing the original direction or the remainder condition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed HolomorphicGermUP HolomorphicGermSealed
  HolomorphicGermRing ComplexWeierstrassDivisionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_division_from_normalization]:
    absorbing the normalizing scalar in Q restores the
    original phi and preserves the actual remainder,
    supporting 3.4.6(1), p. 322. *)
Lemma complex_weierstrass_division_from_normalization (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) k (v:X)
    (C Phi Psi Q T:@holomorphic_germ_ring R X NX hNX 0):
  @is_complex_weierstrass_division R X NX hNX k v (C*Phi) Psi Q T ->
  @is_complex_weierstrass_division R X NX hNX k v Phi Psi (Q*C) T.
Proof.
move=>hDivision;constructor.
- by rewrite -mulrA -(complex_weierstrass_division_identity hDivision).
- exact:complex_weierstrass_division_polynomial_remainder hDivision.
Qed.

(** Source for [complex_weierstrass_division_to_normalization]:
    the inverse scalar sends every original division
    candidate to a normalized one, supporting the germ
    uniqueness assertion of 3.4.6(1), p. 322. *)
Lemma complex_weierstrass_division_to_normalization (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) k (v:X)
    (C D Phi Psi Q T:@holomorphic_germ_ring R X NX hNX 0):
  D*C= 1 ->@is_complex_weierstrass_division R X NX hNX k v Phi Psi Q T ->
  @is_complex_weierstrass_division R X NX hNX k v (C*Phi) Psi (Q*D) T.
Proof.
move=>hInverse hDivision;constructor.
- have hProduct:(Q*D)*(C*Phi)=Q*Phi.
    by rewrite mulrA -[Q*D*C]mulrA hInverse mulr1.
  by rewrite hProduct -(complex_weierstrass_division_identity hDivision).
- exact:complex_weierstrass_division_polynomial_remainder hDivision.
Qed.
