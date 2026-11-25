(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: an
    actual transverse coefficient times a power of xi
    represents the corresponding product in the original
    analytic germ ring. All representatives are local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing HolomorphicGermPowers
  HolomorphicPullbackRepresentative HolomorphicPullbackSealed ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_transverse_monomial_representative]: an
    original coefficient pulled back by eta times xi
    to its original natural exponent has the actual
    product germ, supporting P in 3.4.7, p. 325. *)
Theorem holomorphic_transverse_monomial_representative (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection)
    (fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0)
    (c:@holomorphic_representative_type R K NK (complex_norm_real hNK) (projection 0)) i:
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  exists f:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0,
    (forall x,holomorphic_representative_value f x = (xi x)^+i*holomorphic_representative_value c (projection x)) /\
    (holomorphic_germ f:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0) =
      (@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
        v xi inclusion projection hSplit (holomorphic_germ c))*
      (holomorphic_germ fXi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)^+i.
Proof.
move=>hXi.
have [g [hGValues hGGerm]]:=@holomorphic_representative_power_exists R X NX (complex_norm_real hNX) 0 fXi i.
pose hProjection:=@complex_weierstrass_transverse_projection_holomorphic R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
pose pulled:=@holomorphic_pullback_representative R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) setT projection 0 hProjection c.
exists (@holomorphic_multiply_representatives R X NX (complex_norm_real hNX) 0 pulled g);split.
- move=>x.
  change (holomorphic_representative_value c (projection x)*holomorphic_representative_value g x =
    (xi x)^+i*holomorphic_representative_value c (projection x)).
  by rewrite hGValues hXi mulrC.
- rewrite -(@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX (complex_norm_real hNX) 0)).
  change ((holomorphic_germ pulled:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)*holomorphic_germ g =
    (@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
      v xi inclusion projection hSplit (holomorphic_germ c))*
      (holomorphic_germ fXi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)^+i).
  rewrite hGGerm.
  congr (_*_).
  exact:esym (@HolomorphicPullback.laws R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) setT projection 0 hProjection c).
Qed.
