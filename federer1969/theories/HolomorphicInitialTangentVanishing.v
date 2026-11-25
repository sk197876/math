(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    actual leading Taylor polynomials of functions vanishing
    on the original germ vanish on its tangent cone.
    Use the actual negligible remainder, the existing
    tangent locality law and the homogeneous little-o lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRingLaws HolomorphicGermRepresentatives
  SetGermUP HolomorphicGermVanishingUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative
  HolomorphicInitialPolynomialUP HolomorphicInitialTaylorRemainder TangentConeUP TangentConeLocal
  HomogeneousVectorLittleOTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_initial_polynomial_tangent_vanishes]:
    the first displayed remainder proves that every
    original leading polynomial is zero on Tan(S,0),
    3.4.12, p. 339, extending 3.4.11, p. 338. Original set and
    function representatives are used only through local laws. *)
Theorem holomorphic_initial_polynomial_tangent_vanishes (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (S:set X)
    (alpha:@holomorphic_germ_ring R X NX hNX 0) k (P:X->ComplexScalars.C R):
  @HolomorphicSetIdeal.value R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S) alpha ->
  is_initial_holomorphic_germ_polynomial alpha k P ->
  forall v,@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX S 0 v ->P v=0.
Proof.
move=>hIdeal hInitial v hTangent.
have [f hF]:=@holomorphic_germ_has_representative R X NX hNX 0 alpha.
have hMember:@HolomorphicSetIdeal.value R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S) (holomorphic_germ f).
  by rewrite hF.
have [U [hU [hU0 hVanishing]]]:=
  (@holomorphic_set_ideal_representative_equation R X NX hNX 0 f S).1 hMember.
have hInterior:@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX U 0.
  rewrite openE in hU.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX U 0).2 (hU 0 hU0)).
have [hPolynomial [hContinuous [hScale hRemainder]]]:=
  @holomorphic_initial_taylor_remainder R X NX hNX alpha k P f hInitial hF.
have hLocal:@norm_tangent_cone R (restricted_space (ComplexScalars.embed R) X) NX (S `&` U) 0 v.
  by rewrite (@norm_tangent_open_restriction R (restricted_space (ComplexScalars.embed R) X) NX S U 0 hInterior).
apply:(@homogeneous_vector_little_o_tangent_zero R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) (S `&` U) P k
  hContinuous (fun t x ht=>hScale t x) _ v hLocal).
move=>e he;have [r [hr hR]]:=hRemainder e he.
exists r;split;first exact:hr.
move=>x [hx hUx] hSmall;have hBound:=hR x hSmall.
by rewrite (hVanishing x hx hUx) sub0r (real_seminorm_negate (@complex_modulus_real_norm R).1) in hBound.
Qed.
