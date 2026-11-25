(** Federer (1969), 3.4.12, pp. 338–339, extending 3.1.24,
    p. 240: actual translations are holomorphic on every open
    original domain. Use the proved real affine calculus and
    actual complex first-differential laws for sums and constants. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP ScalarRestriction ComplexScalarSealed NormDifferentialUP
  HolomorphicUP HolomorphicLinear HolomorphicArithmetic HolomorphicNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_translations]: both original affine
    directions used to translate local germ assertions from zero
    to an arbitrary centre, extending 3.4.7, p. 325. *)
Lemma holomorphic_translations (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX)
    (A:X->Prop) (hA:forall x,A x ->norm_domain_interior NX A x) (c:X):
  is_holomorphic hNX hNX A (fun x=>x+c) /\is_holomorphic hNX hNX A (fun x=>x-c).
Proof.
pose Id:Hom X X:=hom_of_linear (linear_id X).
have hBound:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) X) NX NX (complex_hom_real Id).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite /Id /complex_hom_real !hom_of_linearE mul1r.
have hIdentity:=@holomorphic_bounded_linear R X X NX NX hNX hNX A Id hA hBound.
have hConstant:=@holomorphic_constant R X X NX NX hNX hNX A c hA.
split;[exact:holomorphic_add hIdentity hConstant|exact:holomorphic_add hIdentity (holomorphic_negate hConstant)].
Qed.
