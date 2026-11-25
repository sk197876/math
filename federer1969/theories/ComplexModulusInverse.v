(** Federer (1969), 3.4.12, p. 339, extending the denominator
    bounds of 3.4.8(10), p. 332. Multiplicativity and definiteness
    determine the modulus of the original complex inverse. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexModulus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
(** Source for [complex_modulus_inverse]: the inverse denominator
    has modulus equal to the reciprocal modulus, supporting the
    compact-fibre bounds in 3.4.12, p. 339. Zero is retained. *)
Lemma complex_modulus_inverse (R:realType) (z:ComplexScalars.C R):
  complex_modulus z^-1=(complex_modulus z)^-1.
Proof.
have hOne:complex_modulus (1:ComplexScalars.C R) = 1.
  by rewrite -(rmorph1 (ComplexScalars.embed R)) complex_modulus_real normr1.
case:(eqVneq z 0)=>[->|hZ].
- have hZero:complex_modulus (0:ComplexScalars.C R)=0.
    by rewrite -(rmorph0 (ComplexScalars.embed R)) complex_modulus_real normr0.
  by rewrite invr0 hZero invr0.
- have hNorm:(complex_modulus z)!=0 by rewrite complex_modulus_eq0.
  apply:(mulfI hNorm).
  by rewrite -complex_modulus_mul mulfV // hOne mulfV.
Qed.
