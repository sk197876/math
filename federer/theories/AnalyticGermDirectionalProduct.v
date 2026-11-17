(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the actual divided directional coefficients of a
    germ product satisfy the finite convolution law.
    The proof uses the original Leibniz rule of
    3.1.11, p. 222, through actual analytic
    coefficient fields on a common neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormAnalyticUP
  NormAnalyticLocal NormAnalyticOperations NormLinearDomainLaws NormAnalyticScalarProducts AnalyticGermNeighbourhood AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing
  AnalyticDirectionalCoefficient AnalyticDirectionalCoefficientProduct AnalyticGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_directional_coefficient_product]:
    dividing the original diagonal Leibniz formula by
    k! gives the coefficient convolution. Every coefficient
    is an actual derivative of the original germ,
    supporting 3.4.8(5), p. 328, from 3.1.11,
    p. 222, and 3.4.5, p. 319. *)
Theorem analytic_germ_directional_coefficient_product (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a k
  (alpha beta:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) v:
  @analytic_germ_directional_coefficient R X NX hNX a k (alpha*beta) v =
    \sum_(j<k.+1) (@analytic_germ_directional_coefficient R X NX hNX a (k-j)%N alpha v)*
      (@analytic_germ_directional_coefficient R X NX hNX a j beta v).
Proof.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
pose F:=analytic_representative_value f.
pose G:=analytic_representative_value g.
have [U [haU [_ [_ hFU]]]]:=@analytic_germ_open_representative R X R^o NX NS hNX hNS
  setT F a (analytic_representative_analytic f).
have [V [haV [_ [_ hGV]]]]:=@analytic_germ_open_representative R X R^o NX NS hNX hNS
  setT G a (analytic_representative_analytic g).
pose W:=U `&` V.
have ha:W a by split.
have hOpen x (hx:W x):norm_domain_interior NX W x.
  exact:norm_domain_intersection_interior
    ((norm_analytic_class_all_orders hFU 0%N).1 x hx.1).1
    ((norm_analytic_class_all_orders hGV 0%N).1 x hx.2).1.
have hF:=@norm_analytic_open_restriction R X R^o NX NS hNX hNS U W F
  (fun x hx=>hx.1) hOpen hFU.
have hG:=@norm_analytic_open_restriction R X R^o NX NS hNX hNS V W G
  (fun x hx=>hx.2) hOpen hGV.
have hFG:=@norm_analytic_scalar_product R X NX hNX W F G hF hG.
have hEachF i:=@analytic_directional_coefficient_exists R X R^o NX NS hNX hNS W F i v hF.
have hEachG i:=@analytic_directional_coefficient_exists R X R^o NX NS hNX hNS W G i v hG.
have [C hC]:=choice hEachF.
have [D hD]:=choice hEachG.
have [H [hH _]]:=@analytic_directional_coefficient_exists R X R^o NX NS hNX hNS
  W (fun x=>F x*G x) k v hFG.
have hConvolution:=@analytic_directional_coefficient_product R X NX hNX W F G k v a C D H
  ha hF hG (fun i _=>(hC i).1) (fun i _=>(hD i).1) hH.
pose p:=@analytic_multiply_representatives R X NX hNX a f g.
have hRep:analytic_germ p = (alpha*beta:@analytic_germ_ring R X NX hNX a).
  rewrite -hf -hg.
  exact:esym (@analytic_germ_multiply_equation R X NX hNX a _ _ _
    (@AnalyticGerms.laws R X NX hNX a) f g).
have hValue:=@analytic_directional_coefficient_at_germ_centre R X NX hNX a k
  (alpha*beta) p W v H hRep ha hFG hH.
rewrite -hValue hConvolution.
apply:eq_bigr=>j _.
rewrite (@analytic_directional_coefficient_at_germ_centre R X NX hNX a (k-j)%N
  alpha f W v (C (k-j)%N) hf ha hF (hC _).1).
rewrite (@analytic_directional_coefficient_at_germ_centre R X NX hNX a j
  beta g W v (D j) hg ha hG (hD _).1).
reflexivity.
Qed.
