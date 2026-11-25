(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual divided directional coefficients of an analytic
    germ. Their value agrees with every analytic
    coefficient field on every original neighbourhood,
    using the derivatives of 3.1.11, pp. 219–222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormHigherDifferentialUP NormHigherDifferentialLocal NormAnalyticUP NormAnalyticLocal NormRegularity
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticGermJetsSealed
  AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_directional_coefficient]: the
    actual divided directional derivative D^k alpha[v^k]/k!,
    from 3.1.11, pp. 219–222, and the derivative
    germ of 3.4.5, p. 319. This supports the
    expanded Taylor argument for 3.4.8(5), p. 328. *)
Definition analytic_germ_directional_coefficient (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a k
  (alpha:@analytic_germ_ring R X NX hNX a) v:R:=
  ((k`!)%:R:R)^-1*@ContinuousMultilinear.evaluation R k X R^o NX (fun z=>`|z|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
    (@AnalyticGermJets.value R X NX hNX a k alpha).

(** Source for [analytic_directional_coefficient_at_germ_centre]:
    every original analytic directional coefficient field
    gives the same actual germ coefficient, supporting
    3.4.8(5), p. 328, from 3.1.11,
    pp. 219–222, and 3.4.5, p. 319. *)
Lemma analytic_directional_coefficient_at_germ_centre (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a k
  (alpha:@analytic_germ_ring R X NX hNX a)
  (f:@analytic_representative_type R X NX hNX a) (A:set X) v c:
  analytic_germ f = alpha ->A a ->
  @norm_analytic R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value f) ->
  @is_analytic_directional_coefficient R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value f) k v c ->
  c a = @analytic_germ_directional_coefficient R X NX hNX a k alpha v.
Proof.
move=>hRep ha hAnalytic hCoefficient.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z:=fun j=>@ContinuousMultilinear.space R j X R^o NX NS hNX hNS.
pose ev:=fun j=>@ContinuousMultilinear.evaluation R j X R^o NX NS hNX hNS.
pose N:=fun j=>@ContinuousMultilinear.norm R j X R^o NX NS hNX hNS.
have hZ j:=@ContinuousMultilinear.laws R j X R^o NX NS hNX hNS.
have hOpen x (hx:A x):norm_domain_interior NX A x:=
  ((norm_analytic_class_all_orders hAnalytic 0%N).1 x hx).1.
have hActual:=(@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS
  Z ev N hZ k setT A (analytic_representative_value f) (fun x hx=>Logic.I) hOpen a ha
  (@AnalyticGermJets.value R X NX hNX a k alpha)).1
  (@AnalyticGermJets.laws R X NX hNX a k alpha f hRep).
exact:(hCoefficient a ha _ hActual).
Qed.
