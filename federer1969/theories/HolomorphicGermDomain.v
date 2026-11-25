(** Federer (1969), 3.4.12, p. 339:
    the actual holomorphic germ ring has no proper
    zero divisors. Use the original common neighbourhood
    and the existing real connected-domain product theorem
    through actual squared moduli. No formal-series substitute
    for the original functions enters the argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormMetric NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations NormConvexConnected NormLinearDomainLaws
  LocalGermUP LocalGermSealed HolomorphicUP HolomorphicOpenDomain
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives
  HolomorphicGermUP HolomorphicGermOperationsUP HolomorphicGermSealed
  HolomorphicGermRingLaws HolomorphicGermRing AnalyticComplexProductZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_no_zero_divisors]: the
    no-proper-zero-divisor assertion of 3.4.5, p. 319,
    for the actual complex ring specified by 3.4.12,
    p. 339. Both original factors and
    every normed complex source remain; no rank or jet
    hypothesis is added. *)
Theorem holomorphic_germ_no_zero_divisors (R:realType)
    (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X)
    (alpha beta:@holomorphic_germ_ring R X NX hNX a):
  alpha*beta=0 ->alpha=0 \/beta=0.
Proof.
move=>hProduct.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose C:=ComplexScalars.C R.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose NC:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose P:=@holomorphic_representative_type R X NX hNX a.
pose value:=@holomorphic_representative_value R X NX hNX a.
pose germ:=@holomorphic_germ R X NX hNX a.
pose zeroP:=@holomorphic_constant_representative R X NX hNX a 0.
have hG:=@LocalGerms.laws T C P value a.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
have hEqual:germ (@holomorphic_multiply_representatives R X NX hNX a f g)=germ zeroP.
  rewrite /germ /zeroP.
  rewrite -(@holomorphic_germ_multiply_equation R X NX hNX a _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
  rewrite hf hg;exact:hProduct.
have [O [hO [haO hZero]]]:=(local_germ_equality hG _ _).1 hEqual.
have [W [haW [hF hH]]]:=@holomorphic_representatives_common_domain R X NX hNX a f g.
pose U:=fun x=>W x /\O x.
have hOpen x (hx:U x):norm_domain_interior NX U x.
  apply:norm_domain_intersection_interior.
  - exact:(@holomorphic_domain_interior R X C^o NX NC hNX hN W (value f) hF x hx.1).
  - have hONbhs:=hO;rewrite openE in hONbhs.
    exact:((@norm_domain_interior_neighbourhood R XR NX hNX O x).2 (hONbhs x hx.2)).
have haU:U a by split.
have [r [hr hRadius]]:=hOpen a haU.
pose B:=fun x=>NX (x-a)<r.
have hBa:B a by rewrite /B subrr (real_seminorm_zero hNX.1).
have hBInterior x (hx:B x):norm_domain_interior NX B x.
  exact:(@norm_open_ball_domain_interior R XR NX hNX a r x hx).
have hB:@open (real_norm_metric_space hNX) B.
  rewrite openE=>x hx;exact:((@norm_domain_interior_neighbourhood R XR NX hNX B x).1 (hBInterior x hx)).
have hBU x (hx:B x):U x.
  have h:=hRadius (x-a) hx;by rewrite addrC subrK in h.
have hFB:=@norm_analytic_open_restriction R XR CR NX NC hNX hN W B (value f)
  (fun x hx=>(hBU x hx).1) hBInterior hF.1.
have hGB:=@norm_analytic_open_restriction R XR CR NX NC hNX hN W B (value g)
  (fun x hx=>(hBU x hx).1) hBInterior hH.1.
have hConnected:=@norm_inner_convex_connected R XR NX hNX B
  (@norm_open_ball_convex R XR NX hNX a r).
have hProductB x (hx:B x):value f x*value g x=0.
  exact:hZero x (hBU x hx).2.
have hAlternative:=@analytic_complex_product_zero_connected R XR NX hNX B
  (value f) (value g) hConnected hFB hGB hProductB.
case:hAlternative=>hFactor.
- left;rewrite -hf;apply/(local_germ_equality hG).
  exists B;split;first exact:hB;split;first exact:hBa;exact:hFactor.
- right;rewrite -hg;apply/(local_germ_equality hG).
  exists B;split;first exact:hB;split;first exact:hBa;exact:hFactor.
Qed.
