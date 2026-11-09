(** Federer (1969), 3.4.6, pp. 322–323: actual
    coefficient fields of any analytic representative recover
    exactly the original mixed germ coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormHigherDifferentialUP NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsSealed
  AnalyticDirectionalCoefficient WeierstrassCoefficientUP WeierstrassCoefficientValue WeierstrassIteratedCoefficientValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_iterated_germ_coefficient]: the
    original split coefficient equals the iterated divided
    directional coefficient of every original representative,
    3.4.6, pp. 322–323. Actual derivative locality
    and the proved grouping identity discharge the claim. *)
Theorem weierstrass_iterated_germ_coefficient (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (p:analytic_representative_type hNX (0:X)) (A:set X) v (inclusion:Hom K X)
    i j (q:K->R) (C P:X->R) z:
  analytic_germ p=alpha ->A 0 ->
  @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value p) ->
  is_weierstrass_split_coefficient alpha v inclusion i j q ->
  @is_analytic_directional_coefficient R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value p) i v C ->
  @is_analytic_directional_coefficient R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
    A C j (inclusion z) P ->q z = P 0.
Proof.
move=>hRep ha hf hQ hC hP.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose Z k:=@ContinuousMultilinear.space R k X R^o NX N hNX hN.
pose ev k:=@ContinuousMultilinear.evaluation R k X R^o NX N hNX hN.
pose NZ k:=@ContinuousMultilinear.norm R k X R^o NX N hNX hN.
pose hZ k:=@ContinuousMultilinear.laws R k X R^o NX N hNX hN.
have hOpen x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hf 0%N).1 x hx).1.
pose w:=@AnalyticGermJets.value R X NX hNX 0 (i+j)%N alpha.
have hGlobal:=@AnalyticGermJets.laws R X NX hNX 0 (i+j)%N alpha p hRep.
have hLocal:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
  (i+j)%N setT A (analytic_representative_value p) (fun x _=>Logic.I) hOpen 0 ha w).1 hGlobal.
have hValue:=@weierstrass_iterated_coefficient_value R X NX hNX A
  (analytic_representative_value p) 0 v (inclusion z) i j C P w ha hf hC hP hLocal.
by rewrite (weierstrass_split_coefficient_value hQ z) hValue.
Qed.
