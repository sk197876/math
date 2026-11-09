(** Federer (1969), 3.4.6, p. 323: the original
    double-coefficient convolution for products of actual
    analytic germs. The proof uses actual iterated derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormLinearDomainLaws
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormAnalyticScalarProducts
  AnalyticGermNeighbourhood AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws
  AnalyticDirectionalCoefficient AnalyticIteratedDirectionalCoefficients AnalyticIteratedCoefficientProduct
  WeierstrassCoefficientUP WeierstrassIteratedGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_split_coefficient_product]: the
    mixed coefficient of a product is the finite
    two-index convolution of the original mixed coefficients,
    3.4.6, p. 323. Factorial normalization
    cancels both directional Leibniz coefficients. Every
    auxiliary field remains a local existence witness. *)
Theorem weierstrass_split_coefficient_product (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha beta:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) (A B C:nat->nat->K->R):
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (A i j)) ->
  (forall i j,is_weierstrass_split_coefficient beta v inclusion i j (B i j)) ->
  (forall i j,is_weierstrass_split_coefficient (@AnalyticGerms.mul R X NX hNX 0 alpha beta)
    v inclusion i j (C i j)) ->
  forall i j z,C i j z=\sum_(r<i.+1) \sum_(s<j.+1) A (i-r)%N (j-s)%N z*B r s z.
Proof.
move=>hA hB hC i j z.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
have [f hf]:=@analytic_germ_has_representative R X NX hNX 0 alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX 0 beta.
pose F:=analytic_representative_value f.
pose G:=analytic_representative_value g.
have [U [haU [_ [_ hFU]]]]:=@analytic_germ_open_representative R X R^o NX N hNX hN
  setT F 0 (analytic_representative_analytic f).
have [V [haV [_ [_ hGV]]]]:=@analytic_germ_open_representative R X R^o NX N hNX hN
  setT G 0 (analytic_representative_analytic g).
pose W:=U `&` V.
have ha:W 0 by split.
have hOpen x (hx:W x):norm_domain_interior NX W x.
  exact:norm_domain_intersection_interior
    ((norm_analytic_class_all_orders hFU 0%N).1 x hx.1).1
    ((norm_analytic_class_all_orders hGV 0%N).1 x hx.2).1.
have hF:=@norm_analytic_open_restriction R X R^o NX N hNX hN U W F
  (fun x hx=>hx.1) hOpen hFU.
have hG:=@norm_analytic_open_restriction R X R^o NX N hNX hN V W G
  (fun x hx=>hx.2) hOpen hGV.
have hFG:=@norm_analytic_scalar_product R X NX hNX W F G hF hG.
have [D [P [hD hP]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  W F v (inclusion z) hF.
have [E [Q [hE hQ]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  W G v (inclusion z) hG.
have [H [S [hH hS]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  W (fun x=>F x*G x) v (inclusion z) hFG.
pose gamma:=@AnalyticGerms.mul R X NX hNX 0 alpha beta.
pose p:=@analytic_multiply_representatives R X NX hNX 0 f g.
have hRep:analytic_germ p=gamma.
  by rewrite /gamma -hf -hg (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX 0)).
have hOriginal:=@weierstrass_iterated_germ_coefficient R X K NX hNX gamma p W
  v inclusion i j (C i j) (H i) (S i j) z hRep ha hFG (hC i j) (hH i).1 (hS i j).1.
have hConvolution:=@analytic_iterated_coefficient_product R X NX hNX W F G v (inclusion z) 0
  D E P Q i j (H i) (S i j) ha hF hG (fun r=>(hD r).1) (fun r=>(hE r).1)
  (fun r s=>(hP r s).1) (fun r s=>(hQ r s).1) (hH i).1 (hS i j).1.
rewrite hOriginal hConvolution.
apply:eq_bigr=>r _;apply:eq_bigr=>s _.
have hFirst:=@weierstrass_iterated_germ_coefficient R X K NX hNX alpha f W
  v inclusion (i-r)%N (j-s)%N (A (i-r)%N (j-s)%N) (D (i-r)%N) (P (i-r)%N (j-s)%N) z
  hf ha hF (hA _ _) (hD _).1 (hP _ _).1.
have hSecond:=@weierstrass_iterated_germ_coefficient R X K NX hNX beta g W
  v inclusion r s (B r s) (E r) (Q r s) z hg ha hG (hB r s) (hE r).1 (hQ r s).1.
by rewrite -hFirst -hSecond.
Qed.
