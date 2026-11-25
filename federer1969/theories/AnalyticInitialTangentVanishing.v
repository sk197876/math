(** Federer (1969), 3.4.11, p. 338:
    actual leading Taylor polynomials of functions vanishing
    on the original germ vanish on its tangent cone.
    Use the actual negligible remainder, the existing
    tangent locality law and the homogeneous little-o lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws AnalyticGermRepresentatives
  SetGermUP GermVanishingUP GermVanishingSealed GermVanishingRepresentative
  AnalyticInitialPolynomialUP AnalyticInitialTaylorRemainder TangentConeUP TangentConeLocal
  HomogeneousLittleOTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_polynomial_tangent_vanishes]:
    the first displayed remainder proves that every
    original leading polynomial is zero on Tan(S,0),
    3.4.11, p. 338. Original set and
    function representatives are used only through local laws. *)
Theorem analytic_initial_polynomial_tangent_vanishes (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (S:set X)
    (alpha:@analytic_germ_ring R X NX hNX 0) k (P:X->R):
  @AnalyticSetIdeal.value R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S) alpha ->
  is_initial_analytic_germ_polynomial alpha k P ->
  forall v,norm_tangent_cone NX S 0 v ->P v=0.
Proof.
move=>hIdeal hInitial v hTangent.
have [f hF]:=@analytic_germ_has_representative R X NX hNX 0 alpha.
have hMember:@AnalyticSetIdeal.value R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S) (analytic_germ f).
  by rewrite hF.
have [U [hU [hU0 hVanishing]]]:=
  (@analytic_set_ideal_representative_equation R X NX hNX 0 f S).1 hMember.
have hInterior:norm_domain_interior NX U 0.
  rewrite openE in hU.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX U 0).2 (hU 0 hU0)).
have [hPolynomial [hContinuous [hScale hRemainder]]]:=
  @analytic_initial_taylor_remainder R X NX hNX alpha k P f hInitial hF.
have hLocal:norm_tangent_cone NX (S `&` U) 0 v.
  by rewrite (@norm_tangent_open_restriction R X NX S U 0 hInterior).
apply:(@homogeneous_little_o_tangent_zero R X NX hNX (S `&` U) P k
  hContinuous (fun t x ht=>hScale t x) _ v hLocal).
move=>e he;have [r [hr hR]]:=hRemainder e he.
exists r;split;first exact:hr.
move=>x [hx hUx] hSmall;have hBound:=hR x hSmall.
by rewrite (hVanishing x hx hUx) sub0r normrN in hBound.
Qed.
