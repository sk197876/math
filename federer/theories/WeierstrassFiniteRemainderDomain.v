(** Federer (1969), 3.4.6, pp. 322–324: a
    finite polynomial in the distinguished coordinate has
    analytic transverse coefficients on one neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormRegularity NormOpenDomainLaws NormLinearDomainLaws NormAnalyticUP NormAnalyticLocal
  NormAnalyticLinear NormAnalyticOperations NormAnalyticScalarProducts WeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_finite_remainder_domain]: the
    literal finite remainder expression is analytic on one
    open neighbourhood of zero, supporting the division and
    preparation assertions of 3.4.6, pp. 322–324.
    Every coefficient and both coordinate maps retain their
    original domains; no source measurability is required. *)
Theorem weierstrass_finite_remainder_domain (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (U:set X) (f:X->R) k (C:nat->X->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->U 0 ->
  @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R) U f ->
  (forall i,@norm_analytic R X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) U (C i)) ->
  exists A:set X,A 0 /\(forall x,A x ->U x /\U (inclusion (projection x))) /\
    (forall x,A x ->norm_domain_interior NX A x) /\
    @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
      A (fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x))).
Proof.
move=>hSplit hXi ha hf hC.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose eta:=hom_comp inclusion projection.
have hEta:norm_bounded_linear NX NX eta:=norm_bounded_linear_compose
  (weierstrass_transverse_projection_bounded hSplit) (weierstrass_transverse_inclusion_bounded hSplit).
have hU x (hx:U x):norm_domain_interior NX U x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
pose A:=fun x=>U x /\U (eta x).
have hA x (hx:A x):norm_domain_interior NX A x.
  exact:norm_domain_intersection_interior (hU x hx.1)
    (norm_bounded_linear_preimage_interior hNX hEta (hU (eta x) hx.2)).
have haA:A 0 by split;[exact:ha|by rewrite /eta hom_compE !linear0].
have hXiA:=@norm_bounded_linear_analytic R X R^o NX N hNX hN A hA xi hXi.
have hEtaA:=@norm_bounded_linear_analytic R X X NX NX hNX hNX A hA eta hEta.
exists A;split;first exact:haA.
split;first by move=>x hx;exact:hx.
split;first exact:hA.
apply:(@norm_analytic_finite_scalar_sum R X NX hNX A 'I_k
  (fun i x=>(xi x)^+i*C i (inclusion (projection x))) hA)=>i.
have hPower:=@norm_analytic_scalar_power R X NX hNX A xi i hXiA.
have hComposite:=@norm_analytic_compose_on R X X R^o NX NX N hNX hNX hN
  A U eta (C i) (fun x hx=>hx.2) hEtaA (hC i).
exact:(@norm_analytic_scalar_product R X NX hNX A _ _ hPower hComposite).
Qed.
