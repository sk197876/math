(** Federer (1969), 3.4.12, p. 339: inherit the original
    complex norm on a linear subspace. Reuse the established real
    injective pullback theorem; only the complex scalar equation
    needs an additional connection. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealSeminormOperations
  ScalarRestriction ComplexScalarSealed ComplexNormUP HolomorphicLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_norm_injective_precompose]: the inherited
    complex norm on the actual transverse kernel used in 3.4.6,
    p. 322, as extended in 3.4.12, p. 339. *)
Lemma complex_norm_injective_precompose (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NY:Y->R)
    (hNY:is_complex_norm NY) (L:Hom X Y) (hL:injective L):
  is_complex_norm (fun x=>NY (L x)).
Proof.
constructor.
- exact:(@real_norm_injective_precompose R
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y)
    NY (complex_norm_real hNY) (hom_as_linear (complex_hom_real L)) hL).
- move=>c x.
  have hScale:L (c*:x)=c*:L x by rewrite linearZ.
  by rewrite hScale (complex_norm_scale hNY).
Qed.
