(** Federer (1969), 4.1.8, p. 360: repeated
    differentiation preserves the original compact support and
    raises its controlling seminorm order by the word length.
    These supporting estimates reuse the actual ordered test
    operators and one-direction estimates of 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation SmoothDirectionalDerivativeSealed
  SmoothDirectionalSeminormBound TestDirectionalOperator TestDirectionalValues
  DistributionDirectionalDerivative DistributionIteratedDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestIteratedSupportSeminorm.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation Iter := (@distribution_test_iterated_derivative R X Y NX NY hNX hNY
  U hU E ev hE D hD).
Local Notation P := (fun v=>@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY
  U E ev hE D hD v).
Local Notation hP := (fun v=>@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY
  U E ev hE D hD v).
Variable K:smooth_compact_set hNX U.
Local Notation nu := (smooth_function_derivative_seminorm hD K).

(** Source for [test_iterated_derivative_compact_support]: every
    original ordered test derivative stays in the same
    support step, supporting Federer 4.1.8, p. 360.
    The empty word retains the original test itself. *)
Theorem test_iterated_derivative_compact_support s (f:DT):
  @smooth_function_support R X Y NX hNX U E ev (inc f) `<=` smooth_compact_carrier K->
  @smooth_function_support R X Y NX hNX U E ev (inc (Iter s f)) `<=` smooth_compact_carrier K.
Proof.
elim:s f=>[|v s IH] f hK;first exact:hK.
apply:(@distribution_test_directional_derivative_compact_support R X Y NX NY hNX hNY
  U hU E ev hE D hD v K (Iter s f)).
exact:(IH f hK).
Qed.

(** Source for [test_iterated_derivative_seminorm_bound]: the
    original order-r seminorm of an ordered test derivative
    is bounded by a finite multiple of the order
    r plus word-length seminorm on that same K,
    supporting Federer 4.1.8, p. 360. No compact
    enlargement or regularity assumption on a test operator is added. *)
Theorem test_iterated_derivative_seminorm_bound s:
  forall r,exists C:R,0<=C /\forall f:DT,
    nu r (inc (Iter s f))<=C*nu (r+size s)%N (inc f).
Proof.
elim:s=>[|v s IH] r.
- exists 1;split;first exact:ler01.
  by move=>f;rewrite addn0 mul1r.
- have[C [hC hOne]]:=@smooth_directional_seminorm_bound R X Y NX NY hNX hNY U hU
    E ev D hD v (P v) (hP v) K r (nu r) (nu r.+1)
    (smooth_function_derivative_seminorm_laws hD K r)
    (smooth_function_derivative_seminorm_laws hD K r.+1).
  have[B [hB hTail]]:=IH r.+1.
  exists (C*B);split;first exact:mulr_ge0 hC hB.
  move=>f.
  have hFirst:nu r (inc (Iter (v::s) f))<=C*nu r.+1 (inc (Iter s f)).
    change (nu r (inc (@distribution_test_directional_derivative R X Y NX NY hNX hNY
      U hU E ev hE D hD v (Iter s f)))<=C*nu r.+1 (inc (Iter s f))).
    rewrite (@test_directional_evaluation R X Y NX NY hNX hNY U hU E ev hE D hD
      v (P v) (hP v) (Iter s f)).
    exact:(hOne (inc (Iter s f))).
  have hFinal:=le_trans hFirst (ler_wpM2l hC (hTail f)).
  rewrite mulrA addSn in hFinal.
  by rewrite /= addnS;exact:hFinal.
Qed.
End TestIteratedSupportSeminorm.
