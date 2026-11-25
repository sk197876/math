(** Federer (1969), 3.4.6, pp. 321–323: original
    directional regularity gives the lower zero coefficients
    and the nonzero leading divided coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed WeierstrassRegularUP WeierstrassCoefficientUP WeierstrassAxisCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_regular_low_coefficients]: all
    original transverse-degree-zero coefficients below k vanish,
    3.4.6, pp. 322–323. This follows from
    the printed original regularity hypotheses at 0. *)
Lemma weierstrass_regular_low_coefficients (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    k v (inclusion:Hom K X) (C:nat->nat->K->R):
  is_weierstrass_regular_germ alpha k v ->
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (C i j)) ->
  forall i,(i<k)%N ->forall z,C i 0%N z=0.
Proof.
move=>[_ [hLow _]] hC i hi z.
by rewrite (weierstrass_axis_coefficient_value (hC i 0%N) z) (hLow i hi) mulr0.
Qed.

(** Source for [weierstrass_regular_leading_nonzero]: the
    original kth divided directional derivative is nonzero,
    permitting the scalar normalization in 3.4.6, p. 322.
    No normalized leading value is added to the final theorem. *)
Lemma weierstrass_regular_leading_nonzero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X)) k v:
  is_weierstrass_regular_germ alpha k v ->
  ((k`!)%:R)^-1*@ContinuousMultilinear.evaluation R k X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
    (@AnalyticGermJets.value R X NX hNX 0 k alpha)<>0.
Proof.
move=>[_ [_ hNonzero]].
have hFact:((k`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have hValue:@ContinuousMultilinear.evaluation R k X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun _: 'I_k=>v]
    (@AnalyticGermJets.value R X NX hNX 0 k alpha)!=0.
  exact/eqP.
have hInverse:((k`!)%:R:R)^-1!=0 by rewrite invr_eq0;exact:hFact.
apply/eqP;exact:mulf_neq0 hInverse hValue.
Qed.

(** Source for [weierstrass_normalized_leading_coefficient]:
    after the original scalar normalization, phi_(k,0)=1
    at every transverse point, 3.4.6, pp. 322–323.
    This is an auxiliary normalized-case lemma. *)
Lemma weierstrass_normalized_leading_coefficient (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    k v (inclusion:Hom K X) (C:K->R):
  is_weierstrass_split_coefficient alpha v inclusion k 0%N C ->
  ((k`!)%:R)^-1*@ContinuousMultilinear.evaluation R k X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
    (@AnalyticGermJets.value R X NX hNX 0 k alpha)= 1 ->
  forall z,C z= 1.
Proof.
move=>hC hUnit z;by rewrite (weierstrass_axis_coefficient_value hC z).
Qed.
