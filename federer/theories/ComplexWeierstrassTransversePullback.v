(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 325: the actual transverse projection induces the
    original coefficient-ring homomorphism. Use only bounded
    splitting laws and the opaque holomorphic pullback. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  NormDifferentialUP NormOpenDomainLaws HolomorphicUP HolomorphicAtUP HolomorphicLinear
  HolomorphicGermRing HolomorphicPullbackRingMorphism ComplexWeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pullback.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variables (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K).
Variable hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.

(** Source for [complex_weierstrass_transverse_projection_holomorphic]: the
    actual original projection is holomorphic near zero, extending
    3.4.7, p. 325. *)
Lemma complex_weierstrass_transverse_projection_holomorphic:
  @is_holomorphic_at R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) setT projection 0.
Proof.
exists setT;split;first exact:Logic.I.
split;first by move=>x _.
have hHol:=(@holomorphic_bounded_linear R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) setT
  projection (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x) (complex_weierstrass_transverse_projection_bounded hSplit)).
exact:hHol.
Qed.

(** Source for [complex_weierstrass_transverse_ring_pullback]: the
    original induced coefficient-ring homomorphism, extending
    3.4.7, p. 325. Its centre is the actual projection of zero. *)
Definition complex_weierstrass_transverse_ring_pullback:
  {rmorphism [the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)]}:=
  @holomorphic_germ_ring_pullback R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) setT projection 0
    complex_weierstrass_transverse_projection_holomorphic.
End Pullback.
