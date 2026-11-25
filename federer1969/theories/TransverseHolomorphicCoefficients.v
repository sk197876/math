(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 325: actual finite remainder fields restrict to original
    holomorphic coefficient germs on the transverse kernel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm NormDifferentialUP NormOpenDomainLaws HolomorphicUP HolomorphicLinear
  HolomorphicComposition HolomorphicGermRepresentatives ComplexWeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [transverse_holomorphic_coefficient_representative]: actual
    divided fields composed with the original inclusion supply the
    coefficient germs, extending 3.4.7, p. 325. All
    coefficient functions retain their original total values. *)
Theorem transverse_holomorphic_coefficient_representative (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (NK:K->R)
    (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (F:X->ComplexScalars.C R) (U:set X):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->U 0 ->
  is_holomorphic (complex_norm_real hNX) (@complex_modulus_real_norm R) U F ->
  exists c:@holomorphic_representative_type R K NK (complex_norm_real hNK) (projection 0),
    forall z,holomorphic_representative_value c z=F (inclusion z).
Proof.
move=>hSplit haU hF.
have hInclusion:=@holomorphic_bounded_linear R K X NK NX (complex_norm_real hNK) (complex_norm_real hNX)
  setT inclusion (fun z _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) K) NK z) (complex_weierstrass_transverse_inclusion_bounded hSplit).
have hComposite:=holomorphic_composition hInclusion hF.
have hCentre:(fun z=>setT z /\U (inclusion z)) (projection 0).
  split;first exact:Logic.I.
  by rewrite !linear0.
have [c hValues]:=@holomorphic_representative_from_domain R K NK (complex_norm_real hNK) (projection 0)
  (fun z=>setT z /\U (inclusion z)) (fun z=>F (inclusion z)) hCentre hComposite.
exists c=>z;by rewrite hValues.
Qed.
