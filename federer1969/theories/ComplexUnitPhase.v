(** Federer (1969), 1.8.2, p. 39, proof of Hermitian Cauchy's inequality:
    choose c with |c|=1 and H(v,cw) real. The local scalar result below
    chooses a phase making a given nonzero complex scalar positive real.
    Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  ComplexModulusUP ComplexModulus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Phase.
Variable R : rcfType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).

(** Source for [complex_modulus_conjugate]: Federer 1.8.2,
    p. 39, supporting invariance of absolute value under conjugation. *)
Lemma complex_modulus_conjugate (z : C) : complex_modulus (conjugate z) = complex_modulus z.
Proof.
apply: (complex_modulus_unique (complex_modulusP _)); constructor.
- exact: complex_modulus_ge0.
- by rewrite complex_modulus_sqr /norm_square re_conjugate im_conjugate sqrrN.
Qed.

(** Source for [complex_positive_phase_exists]: Federer 1.8.2,
    p. 39, the phase used in the Cauchy proof can make the
    scalar positive real, not merely real, when it is nonzero. *)
Theorem complex_positive_phase_exists (z : C) : z != 0 ->
  exists c : C, complex_modulus c = 1 /\ z*c = embed (complex_modulus z).
Proof.
move=> hz; pose r := complex_modulus z.
have hr : 0 < r := complex_modulus_gt0 hz.
have hr0 : r != 0 by rewrite gt_eqF.
have her : embed r != 0 by rewrite fmorph_eq0.
pose c := conjugate z / embed r.
have hce : c * embed r = conjugate z by rewrite /c divfK.
have hc : complex_modulus c = 1.
  have hh := congr1 (@complex_modulus R) hce.
  rewrite complex_modulus_mul complex_modulus_real complex_modulus_conjugate
    (ger0_norm (ltW hr)) in hh.
  apply: (mulIf hr0).
  by rewrite mul1r.
exists c; split=> //.
rewrite /c mulrA mul_conjugate -complex_modulus_sqr.
change (embed (r^+2) / embed r = embed r).
by rewrite rmorphXn expr2 -mulrA mulfV // mulr1.
Qed.
End Phase.
