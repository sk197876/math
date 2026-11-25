(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5),
    pp. 326, 328: bounded original complex coordinates shifted
    to an arbitrary centre have actual holomorphic representatives.
    Use the proved holomorphic linear maps, translations and composition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  NormDifferentialUP NormOpenDomainLaws HolomorphicUP HolomorphicLinear HolomorphicTranslations
  HolomorphicFiniteCalculus HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pointed_holomorphic_functional_representative_exists]: an
    actual original coordinate xi(x-a) represents its pointed
    germ, extending 3.4.8(1),(5), pp. 326, 328.
    Its construction serves only to prove existence. *)
Theorem pointed_holomorphic_functional_representative_exists (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a
    (xi:Hom X (ComplexScalars.C R)^o):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) (complex_hom_real xi) ->
  exists f:@holomorphic_representative_type R X NX (complex_norm_real hNX) a,
    forall x,holomorphic_representative_value f x=xi (x-a).
Proof.
move=>hXi.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose hNXR:=complex_norm_real hNX.
have hLinear:=@holomorphic_bounded_linear R X (ComplexScalars.C R)^o NX (@complex_modulus R)
  hNXR (@complex_modulus_real_norm R) setT xi
  (fun x _=>@norm_full_domain_interior R XR NX x) hXi.
have hTranslate:=(@holomorphic_translations R X NX hNXR setT
  (fun x _=>@norm_full_domain_interior R XR NX x) a).2.
have hComposite:=@holomorphic_compose_on R X X (ComplexScalars.C R)^o NX NX (@complex_modulus R)
  hNXR hNXR (@complex_modulus_real_norm R) setT setT
  (fun x=>x-a) xi (fun x _=>Logic.I) hTranslate hLinear.
have [f hF]:=@holomorphic_representative_from_domain R X NX hNXR a setT (fun x=>xi (x-a)) Logic.I hComposite.
exists f=>x;by rewrite hF.
Qed.
