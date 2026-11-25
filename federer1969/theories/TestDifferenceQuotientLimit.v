(** Federer (1969), 4.1.1, p. 346: the
    actual test-function Taylor quotient error
    converges to zero in Federer's literal final
    topology. One compact support bound and the
    original finite derivative seminorm limits
    prove this assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws LinearBasis ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothFunctionTopology
  SmoothDirectionalDerivativeSealed SmoothGlobalTranslationSealed TestGlobalTranslation
  TestDirectionalOperator DistributionDirectionalDerivative SmoothDifferenceQuotientJets
  SmoothDifferenceErrorCompactSupport SmoothDifferenceQuotientSeminorm SmoothSupportedPuncturedLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TestDifferenceQuotient.
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

(** Source for [test_difference_quotient_error]: the
    actual test function x |-> [phi(x+tv)-phi(x)]/t
    minus D_v phi, Federer 4.1.1, p. 346. *)
Definition test_difference_quotient_error (t:R) (f:DT):DT:=t^-1*:(A (t*:v) f-f)-Q f.

(** Source for [test_difference_quotient_error_inclusion]:
    inclusion into E preserves the original
    quotient error, supporting Federer 4.1.1,
    p. 346. *)
Lemma test_difference_quotient_error_inclusion t f:
  inc (test_difference_quotient_error t f)=err t (inc f).
Proof.
have hScale:inc (t^-1*:(A (t*:v) f-f))=t^-1*:inc (A (t*:v) f-f):=
  linearZ_LR (hom_as_linear inc) t^-1 (A (t*:v) f-f).
have hOuter:inc (test_difference_quotient_error t f)=
  inc (t^-1*:(A (t*:v) f-f))-inc (Q f).
  exact:(linearB (hom_as_linear inc) (t^-1*:(A (t*:v) f-f)) (Q f)).
have hInner:inc (A (t*:v) f-f)=inc (A (t*:v) f)-inc f.
  exact:(linearB (hom_as_linear inc) (A (t*:v) f) f).
rewrite hOuter hScale hInner
  (@test_global_translation_inclusion R X Y NX NY hNX hNY E ev hE (t*:v) (L (t*:v)) (hL (t*:v)))
  (@test_directional_evaluation R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v P hP).
reflexivity.
Qed.

(** Source for [test_difference_quotient_limit]: the original
    difference-quotient errors converge to zero
    in D for every compactly supported smooth
    test, Federer 4.1.1, p. 346. The
    literal final topology is retained throughout. *)
Theorem test_difference_quotient_limit f:
  forall B,smooth_test_opens hE hD B ->B 0 ->exists r:R,0<r /\ forall t,
    0<`|t|<r ->B (test_difference_quotient_error t f).
Proof.
have [K hK]:=smooth_test_support_bound hE f.
have [C hC]:=@smooth_difference_error_common_support R X Y NX NY hNX hNY d b hb E ev hE D hD
  v P hP L hL K (inc f) hK.
apply:(@smooth_supported_punctured_limit R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD
  (fun t=>test_difference_quotient_error t f) C 1 ltr01).
- move=>t ht; rewrite test_difference_quotient_error_inclusion; exact:hC t (ltW ht).
- move=>J i e he.
  have [r [hr hSemBound]]:=@smooth_difference_quotient_seminorm_limit R X Y NX NY hNX hNY E ev hE D hD
    v P hP L hL (inc f) J i e he.
  exists r; split=>// t ht; rewrite test_difference_quotient_error_inclusion; exact:hSemBound t ht.
Qed.
End TestDifferenceQuotient.
