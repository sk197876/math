(** Federer (1969), 3.4.12, p. 339: the original finite
    transverse remainder is holomorphic on one actual neighbourhood.
    Reuse bounded coordinate maps, the independent transverse laws
    and the proved finite holomorphic calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormDifferentialLinear NormBoundedLinearTopology
  NormLinearDomainLaws NormRegularity NormAnalyticLocal HolomorphicUP HolomorphicLinear
  HolomorphicOpenDomain HolomorphicFiniteCalculus HolomorphicProduct
  ComplexWeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Domain.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNKR:=(complex_norm_real hNK).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_finite_remainder_domain]: one
    neighbourhood supports the entire finite original remainder,
    extending 3.4.6, pp. 322–324, under 3.4.12, p. 339.
    The original coordinate maps and every coefficient retain their domains. *)
Theorem complex_weierstrass_finite_remainder_domain v (xi:Hom X C^o)
    (inclusion:Hom K X) (projection:Hom X K) (U:set X) (f:X->C) k (D:nat->X->C):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R XR CR NX N (complex_hom_real xi) ->U 0 ->
  is_holomorphic hNXR hN U f ->
  (forall i,is_holomorphic hNXR hN U (D i)) ->
  exists A:set X,A 0 /\(forall x,A x ->U x /\U (inclusion (projection x))) /\
    (forall x,A x ->@norm_domain_interior R XR NX A x) /\
    is_holomorphic hNXR hN A (fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x))).
Proof.
move=>hSplit hXi ha hf hD.
pose eta:=hom_comp inclusion projection.
have hEta:@norm_bounded_linear R XR XR NX NX (complex_hom_real eta).
  exact:norm_bounded_linear_compose
    (complex_weierstrass_transverse_projection_bounded hSplit)
    (complex_weierstrass_transverse_inclusion_bounded hSplit).
have hU x (hx:U x):@norm_domain_interior R XR NX U x.
  exact:holomorphic_domain_interior hf x hx.
pose A:=fun x=>U x /\U (eta x).
have hA x (hx:A x):@norm_domain_interior R XR NX A x.
  exact:norm_domain_intersection_interior (hU x hx.1)
    (norm_bounded_linear_preimage_interior hNXR hEta (hU (eta x) hx.2)).
have haA:A 0 by split;[exact:ha|by rewrite /eta hom_compE !linear0].
have hXiA:=@holomorphic_bounded_linear R X C^o NX N hNXR hN A xi hA hXi.
have hEtaA:=@holomorphic_bounded_linear R X X NX NX hNXR hNXR A eta hA hEta.
exists A;split;first exact:haA.
split;first by move=>x hx;exact:hx.
split;first exact:hA.
apply:(@holomorphic_finite_sum R X C^o NX N hNXR hN A 'I_k
  (fun i x=>(xi x)^+i*D i (inclusion (projection x))) hA)=>i.
have hPower:=@holomorphic_scalar_power R X NX hNXR A xi i hXiA.
have hComposite:=@holomorphic_compose_on R X X C^o NX NX N hNXR hNXR hN
  A U eta (D i) (fun x hx=>hx.2) hEtaA (hD i).
exact:holomorphic_product hPower hComposite.
Qed.
End Domain.
