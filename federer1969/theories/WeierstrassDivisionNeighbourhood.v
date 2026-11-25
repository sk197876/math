(** Federer (1969), 3.4.6(1), p. 322: the
    actual quotient and remainder satisfy the printed
    function equation and every derivative condition on
    one original neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormLinearDomainLaws
  NormBoundedLinearTopology NormAnalyticUP NormAnalyticLocal NormAnalyticOperations
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  LocalGermUP LocalGermSealed AnalyticGermNeighbourhood AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing WeierstrassDivisionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_division_on_neighbourhood]:
    the original germ laws give actual analytic functions
    Q,R with psi=Q phi+R and every required directional
    derivative of R zero on one neighbourhood,
    3.4.6(1), p. 322. Original representatives
    of phi and psi are retained; no representative
    equation is an additional hypothesis. *)
Theorem weierstrass_division_on_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) k (v:X)
    (Phi Psi Q T:@analytic_germ_ring R X NX hNX 0)
    (phi psi:analytic_representative_type hNX (0:X)):
  analytic_germ phi=Phi ->analytic_germ psi=Psi ->
  @is_weierstrass_division R X NX hNX k v Phi Psi Q T ->
  exists q r:analytic_representative_type hNX (0:X),
    analytic_germ q=Q /\analytic_germ r=T /\
    exists A:set X,A 0 /\open (A:set (real_norm_metric_space hNX)) /\
      @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value q) /\
      @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value r) /\
      (forall x,A x ->analytic_representative_value psi x=
        analytic_representative_value q x*analytic_representative_value phi x+analytic_representative_value r x) /\
      forall i,(k<=i)%N ->forall x,A x ->
        forall z:@ContinuousMultilinear.space R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R),
        has_norm_higher_differential NX
          (fun j=>@ContinuousMultilinear.evaluation R j X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
          (fun j=>@ContinuousMultilinear.norm R j X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R))
          setT (analytic_representative_value r) i x z ->
        @ContinuousMultilinear.evaluation R i X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
          [ffun _:'I_i=>v] z=0.
Proof.
move=>hPhi hPsi hDivision.
have [r [hR [U [haU [hr hVanish]]]]]:=weierstrass_division_polynomial_remainder hDivision.
have [q hQ]:=@analytic_germ_has_representative R X NX hNX 0 Q.
pose product:=@analytic_multiply_representatives R X NX hNX 0 q phi.
pose sum:=@analytic_add_representatives R X NX hNX 0 product r.
have hRepSum:analytic_germ sum=Q*Phi+T.
  change (analytic_germ sum=@AnalyticGerms.add R X NX hNX 0 (@AnalyticGerms.mul R X NX hNX 0 Q Phi) T).
  rewrite -hQ -hPhi -hR
    (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0))
    (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0)).
  reflexivity.
have hGermEqual:analytic_germ psi=analytic_germ sum.
  by rewrite hPsi hRepSum -(weierstrass_division_identity hDivision).
pose TX:=Topological.clone (real_norm_metric_space hNX) _.
have hGerms:=@LocalGerms.laws TX R (@analytic_representative_type R X NX hNX 0)
  (@analytic_representative_value R X NX hNX 0) 0.
have [O [hO [haO hEquation]]]:=(local_germ_equality hGerms _ _).1 hGermEqual.
have [V [haV [_ [_ hq]]]]:=@analytic_germ_open_representative R X R^o NX (fun t=>`|t|)
  hNX (@scalar_absolute_value_norm R) setT (analytic_representative_value q) 0 (analytic_representative_analytic q).
pose A:=fun x=>U x /\V x /\O x.
have hOpen x (hx:A x):norm_domain_interior NX A x.
  have hONbhs:=hO;rewrite openE in hONbhs.
  exact:norm_domain_intersection_interior ((norm_analytic_class_all_orders hr 0%N).1 x hx.1).1
    (norm_domain_intersection_interior ((norm_analytic_class_all_orders hq 0%N).1 x hx.2.1).1
      ((@norm_domain_interior_neighbourhood R X NX hNX O x).2 (hONbhs x hx.2.2))).
exists q,r;split;first exact:hQ.
split;first exact:hR.
exists A;split;first by split;[exact:haU|split;[exact:haV|exact:haO]].
split.
- rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX A x).1 (hOpen x hx).
split.
- exact:(@norm_analytic_open_restriction R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    V A (analytic_representative_value q) (fun x hx=>hx.2.1) hOpen hq).
split.
- exact:(@norm_analytic_open_restriction R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    U A (analytic_representative_value r) (fun x hx=>hx.1) hOpen hr).
split.
- move=>x hx;exact:hEquation x hx.2.2.
- move=>i hi x hx;exact:hVanish i hi x hx.1.
Qed.
