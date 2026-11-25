(** Federer (1969), 3.4.5, p. 319: the analytic
    germ ring has no proper divisors of zero. The proof
    expands this local assertion through the identity theorem
    of 3.1.24 on an actual connected norm ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations NormConvexConnected NormLinearDomainLaws
  LocalGermUP LocalGermSealed AnalyticGermNeighbourhood AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing AnalyticProductZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_no_zero_divisors]: the phrase
    "has no proper divisors of 0" in 3.4.5, p. 319.
    An actual product germ is zero only if one original factor
    germ is zero. Neither factor is supplied with an additional
    rank, jet or vanishing hypothesis; no completeness is needed. *)
Theorem analytic_germ_no_zero_divisors (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha beta:@analytic_germ_ring R X NX hNX a):
  alpha*beta=0 ->alpha=0 \/beta=0.
Proof.
move=>hProduct.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
pose germ:=@analytic_germ R X NX hNX a.
pose zeroP:=@analytic_constant_representative R X NX hNX a 0.
have hG:=@LocalGerms.laws T R P value a.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
have hEqual:germ (@analytic_multiply_representatives R X NX hNX a f g)=germ zeroP.
  rewrite /germ /zeroP.
  rewrite -(@analytic_germ_multiply_equation R X NX hNX a _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
  rewrite hf hg;exact:hProduct.
have [O [hO [haO hZero]]]:=(local_germ_equality hG _ _).1 hEqual.
have [U [haU [hUT [hU hfU]]]]:=analytic_germ_open_representative (analytic_representative_analytic f).
have [V [haV [hVT [hV hgV]]]]:=analytic_germ_open_representative (analytic_representative_analytic g).
pose C:=U `&` (V `&` O).
have hC:@open (real_norm_metric_space hNX) C:=openI hU (openI hV hO).
have haC:C a by split;[exact:haU|split;[exact:haV|exact:haO]].
have hCNbhs:=hC;rewrite openE in hCNbhs.
have [r [hr hRadius]]:=(@norm_domain_interior_neighbourhood R X NX hNX C a).2 (hCNbhs a haC).
pose B:=fun x=>NX (x-a)<r.
have hBa:B a by rewrite /B subrr (real_seminorm_zero hNX.1).
have hBInterior x (hx:B x):norm_domain_interior NX B x.
  exact:(@norm_open_ball_domain_interior R X NX hNX a r x hx).
have hB:@open (real_norm_metric_space hNX) B.
  rewrite openE=>x hx;exact:((@norm_domain_interior_neighbourhood R X NX hNX B x).1 (hBInterior x hx)).
have hBC x (hx:B x):C x.
  have hh:=hRadius (x-a) hx;by rewrite addrC subrK in hh.
have hF:=@norm_analytic_open_restriction R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
  U B (value f) (fun x hx=>(hBC x hx).1) hBInterior hfU.
have hH:=@norm_analytic_open_restriction R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
  V B (value g) (fun x hx=>(hBC x hx).2.1) hBInterior hgV.
have hConnected:=@norm_inner_convex_connected R X NX hNX B
  (@norm_open_ball_convex R X NX hNX a r).
have hProductB x (hx:B x):value f x*value g x=0.
  exact:hZero x (hBC x hx).2.2.
have hAlternative:=@analytic_product_zero_connected R X NX hNX B (value f) (value g)
  hConnected hF hH hProductB.
case:hAlternative=>hFactor.
- left;rewrite -hf.
  apply/(local_germ_equality hG).
  exists B;split;first exact:hB.
  split;first exact:hBa.
  exact:hFactor.
- right;rewrite -hg.
  apply/(local_germ_equality hG).
  exists B;split;first exact:hB.
  split;first exact:hBa.
  exact:hFactor.
Qed.
