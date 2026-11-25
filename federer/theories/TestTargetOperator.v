(** Federer (1969), 4.1.7, pp. 355–356: actual
    continuous coefficient maps on the original test
    spaces. Their construction uses the opaque smooth
    operator and the proved fixed-support lifting law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothTargetOperatorUP SmoothTargetOperatorSealed SmoothTargetOperatorSupport
  SmoothTargetOperatorContinuity SupportedSmoothOperatorTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section TestTargetOperator.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:set X.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation Pjet := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation Qjet := (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ).
Variable D:forall j,X->Hom E (Pjet j).
Variable G:forall j,X->Hom F (Qjet j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X Z NX NZ hNX hNZ U F fv G.
Variable L:Hom Y Z.
Hypothesis hL:norm_bounded_linear NY NZ L.
Local Notation P := (@SmoothTargetOperator.operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL).
Local Notation hP := (@SmoothTargetOperator.laws R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL).
Local Notation hSupport := (@smooth_target_operator_preserves_support R X Y Z NX NZ
  hNX hNZ U E F ev fv hF L P hP).

(** Source for [test_target_operator]: the actual map
    on compact tests induced by the bounded linear
    coefficient map, supporting Federer 4.1.7,
    pp. 355–356. *)
Definition test_target_operator:Hom (smooth_test_space hE) (smooth_test_space hF):=
  @supported_smooth_test_operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF P hSupport.

(** Source for [test_target_operator_inclusion]: the
    actual test operator agrees with its smooth
    operator, supporting Federer 4.1.7, pp. 355–356. *)
Lemma test_target_operator_inclusion f:
  smooth_test_inclusion hF (test_target_operator f)= P (smooth_test_inclusion hE f).
Proof. exact:supported_smooth_test_evaluation. Qed.

(** Source for [test_target_operator_value]: exact
    pointwise coefficient action on every original
    test, supporting Federer 4.1.7, pp. 355–356. *)
Theorem test_target_operator_value f x:
  U x->smooth_test_value hF (test_target_operator f) x=L (smooth_test_value hE f x).
Proof.
move=>hx; rewrite /smooth_test_value test_target_operator_inclusion.
exact:(@hP (smooth_test_inclusion hE f) x hx).
Qed.

(** Source for [test_target_operator_continuous]: the
    actual coefficient operator is continuous for the
    original literal final topology on tests,
    supporting Federer 4.1.7, pp. 355–356. *)
Theorem test_target_operator_continuous:
  open_family_continuous (smooth_test_opens hE hD) (smooth_test_opens hF hG)
    test_target_operator.
Proof.
exact:(@supported_smooth_test_continuous R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF D G hD hG
  P hSupport (@smooth_target_operator_continuous R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF
    D G hD hG L hL P hP)).
Qed.
End TestTargetOperator.
