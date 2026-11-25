(** Federer (1969), 4.1.1, p. 346: applying
    a distribution to the original test quotient
    gives the printed scalar limit. Continuity
    and the actual D-topology Taylor limit prove
    it with no differentiation axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws LinearBasis ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothFunctionTopology
  SmoothDirectionalDerivativeSealed SmoothGlobalTranslationSealed TestGlobalTranslation
  TestDirectionalOperator DistributionDirectionalDerivative SmoothDifferenceQuotientJets
  TestDifferenceQuotientLimit ContinuousRealDual NormOpenTopology RealOpenSequenceFacts NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionQuotientFormula.
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
Variable v:X.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Local Notation P := (@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v).
Local Notation hP := (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation Q := (@distribution_test_directional_derivative R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).
Local Notation err := (@smooth_difference_quotient_error R X E v P L).

Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation testError := (@test_difference_quotient_error R X Y NX NY hNX hNY E ev hE D hD v).

(** Source for [distribution_difference_quotient_formula]:
    (TD_v)(phi) is the limit of the translated
    scalar quotients, the displayed conclusion
    in Federer 4.1.1, p. 346. *)
Theorem distribution_difference_quotient_formula (T:DD) f:
  punctured_norm_limit (fun t:R^o=>`|t|)
    (fun t=>t^-1*(eD T (A (t*:v) f)-eD T f)) (eD T (Q f)).
Proof.
move=>e he.
pose B:=[set g:DT | `|eD T g-0|<e].
have hT:=@continuous_real_dual_member_continuous R DT SO hSO T.
have hB:SO B:=hT _ (@real_open_scalar_ball R 0 e).
have hZero:B 0 by rewrite /B /= linear0 subrr normr0.
have [r [hr hbLimit]]:=@test_difference_quotient_limit R X Y NX NY hNX hNY d b hb E ev hE D hD
  v f B hB hZero.
exists r; split=>// t ht.
have hSmall:=hbLimit t ht.
have hOuter:eD T (testError t f)=eD T (t^-1*:(A (t*:v) f-f))-eD T (Q f).
  exact:(linearB (hom_as_linear (eD T)) (t^-1*:(A (t*:v) f-f)) (Q f)).
have hScale:eD T (t^-1*:(A (t*:v) f-f))=t^-1*:eD T (A (t*:v) f-f):=
  linearZ_LR (hom_as_linear (eD T)) t^-1 (A (t*:v) f-f).
have hInner:eD T (A (t*:v) f-f)=eD T (A (t*:v) f)-eD T f.
  exact:(linearB (hom_as_linear (eD T)) (A (t*:v) f) f).
change (is_true (`|eD T (testError t f)-0|<e)) in hSmall.
by rewrite hOuter hScale hInner subr0 in hSmall.
Qed.
End DistributionQuotientFormula.
