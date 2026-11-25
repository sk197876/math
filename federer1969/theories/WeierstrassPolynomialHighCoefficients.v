(** Federer (1969), 3.4.6(1), pp. 321–324:
    the original neighbourhood derivative condition forces
    all high distinguished rows of the actual mixed array
    to vanish. This supports uniqueness of division. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormRegularity NormHigherDifferentialUP NormHigherDifferentialLocal
  NormAnalyticUP NormAnalyticLocal NormAnalyticHigherJet NormTaylorLineValues
  AnalyticGermUP AnalyticGermRepresentatives AnalyticDirectionalCoefficient
  AnalyticDirectionalPolynomialLine WeierstrassDivisionUP WeierstrassCoefficientUP
  WeierstrassIteratedGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_polynomial_high_coefficients]:
    every actual candidate remainder has all mixed coefficients
    of distinguished degree at least k zero, supporting
    the original uniqueness claim of 3.4.6(1), p. 322.
    The proof differentiates actual zero coefficient fields
    on the original neighbourhood; no coefficient vanishing
    is added to the numbered theorem's hypotheses. *)
Theorem weierstrass_polynomial_high_coefficients (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) k (v:X) (inclusion:Hom K X)
    (rho:analytic_germ_space hNX (0:X)) (r:nat->nat->K->R):
  @is_directional_polynomial_germ R X NX hNX k v rho ->
  (forall i j,is_weierstrass_split_coefficient rho v inclusion i j (r i j)) ->
  forall i,(k<=i)%N ->forall j z,r i j z=0.
Proof.
move=>[f [hRep [U [ha [hf hVanish]]]]] hR i hi j z.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z m:=@ContinuousMultilinear.space R m X R^o NX N hNX hN.
pose ev m:=@ContinuousMultilinear.evaluation R m X R^o NX N hNX hN.
pose NZ m:=@ContinuousMultilinear.norm R m X R^o NX N hNX hN.
pose hZ m:=@ContinuousMultilinear.laws R m X R^o NX N hNX hN.
pose F:=analytic_representative_value f.
have hOpen x (hx:U x):norm_domain_interior NX U x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
have [C [hC hAnalyticC]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN U F i v hf.
have [D [hD _]]:=@norm_analytic_higher_jet_exists R X R^o NX N hNX hN i U F hf.
have hZero x (hx:U x):C x=0.
  have hFull:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
    i setT U F (fun x _=>Logic.I) hOpen x hx (D x)).2 (hD x hx).
  have hValue:=hVanish i hi x hx (D x) hFull.
  rewrite (hC x hx (D x) (hD x hx)) hValue scaler0.
  reflexivity.
have [P [hP _]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN U C j (inclusion z) hAnalyticC.
have hOriginal:=@weierstrass_iterated_germ_coefficient R X K NX hNX rho f U v inclusion
  i j (r i j) C P z hRep ha hf (hR i j) hC hP.
have [delta [hDelta hBall]]:=hOpen 0 ha.
have [radius [hRadius hSmall]]:=@norm_scalar_line_small_increments R X NX hNX (inclusion z) delta hDelta.
have hLine t (ht:`|t|<radius):C (0+t*:inclusion z)=\sum_(m<0) t^+m*:(0:R^o).
  rewrite big_ord0;apply:hZero;exact:hBall _ (hSmall t ht).
have hFinite:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN
  U C j (inclusion z) 0 P 0%N (fun _=>0) radius ha hAnalyticC hP hRadius hLine.
by rewrite hOriginal ltn0 in hFinite *.
Qed.
