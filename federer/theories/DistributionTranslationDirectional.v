(** Federer (1969), 4.1.8, p. 360: the derivative of a
    current applied to a parameter slice is obtained by
    differentiating the test. This supporting identity applies
    the actual quotient limit of 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  LinearBasis ContinuousMultilinearSealed SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  SmoothGlobalTranslationSealed TestGlobalTranslation TestGlobalTranslationLaws
  DistributionDirectionalDerivative DistributionQuotientFormula
  TestTranslationDirectionalCommutation ContinuousRealDual NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DistributionTranslationDirectional.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).
Local Notation Q := (fun v=>@distribution_test_directional_derivative R X Y NX NY hNX hNY
  (fun _=>True) hFull E ev hE D hD v).

(** Source for [distribution_translation_orbit_directional]: for
    every direction v, the derivative at c of T(f(.+c))
    is T((D_v f)(.+c)). This supports the original
    smooth slice in Federer 4.1.8, p. 360, using
    the original two-sided quotient of 4.1.1, p. 346. *)
Theorem distribution_translation_orbit_directional (T:DD) (f:DT) c v:
  punctured_norm_limit (fun t:R^o=>`|t|)
    (fun t=>t^-1*(eD T (A (c+t*:v) f)-eD T (A c f)))
    (eD T (A c (Q v f))).
Proof.
have h:=@distribution_difference_quotient_formula R X Y NX NY hNX hNY
  d b hb E ev hE D hD v T (A c f).
have hValue:forall t,A (t*:v) (A c f)=A (c+t*:v) f.
  move=>t; by rewrite (@test_global_translation_composition R X Y NX NY hNX hNY E ev hE) addrC.
have hDerivative:Q v (A c f)=A c (Q v f).
  exact:(@test_translation_directional_commutation R X Y NX NY hNX hNY E ev hE D hD v c f).
move=>epsilon hEpsilon.
have[r [hr hSmall]]:=h epsilon hEpsilon.
exists r;split;first exact:hr.
move=>t ht.
have hAt:=hSmall t ht.
by rewrite (@hValue t) hDerivative in hAt.
Qed.
End DistributionTranslationDirectional.
