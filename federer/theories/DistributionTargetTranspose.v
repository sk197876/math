(** Federer (1969), 4.1.7, pp. 355–356: fixed
    bounded coefficient operations induce actual weakly
    continuous maps on distributions by transposition.
    All test maps use the original literal final topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces
  SmoothTestTopology ContinuousRealDual ContinuousRealDualTranspose TestTargetOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section DistributionTargetTranspose.
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
Local Notation TE := (smooth_test_space hE).
Local Notation TF := (smooth_test_space hF).
Local Notation OE := (smooth_test_opens hE hD).
Local Notation OF := (smooth_test_opens hF hG).
Local Notation hOE := (smooth_test_final_topology_laws hE hD).1.
Local Notation hOF := (smooth_test_final_topology_laws hF hG).1.
Local Notation DE := (@continuous_real_dual_space R TE OE hOE).
Local Notation DF := (@continuous_real_dual_space R TF OF hOF).
Local Notation eE := (@continuous_real_dual_evaluation R TE OE hOE).
Local Notation eF := (@continuous_real_dual_evaluation R TF OF hOF).
Local Notation P := (@test_target_operator R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF L hL).
Local Notation hP := (@test_target_operator_continuous R X Y Z NX NY NZ hNX hNY hNZ U E F ev fv hE hF
  D G hD hG L hL).

(** Source for [distribution_target_transpose]: the actual
    coefficient transpose used to construct current
    operations, Federer 4.1.7, pp. 355–356. *)
Definition distribution_target_transpose:Hom DF DE:=
  @continuous_real_dual_transpose R TE TF OE OF hOE hOF P hP.

(** Source for [distribution_target_transpose_evaluation]:
    exact original test action, supporting Federer
    4.1.7, pp. 355–356. *)
Lemma distribution_target_transpose_evaluation T f:
  eE (distribution_target_transpose T) f=eF T (P f).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [distribution_target_transpose_continuous]:
    coefficient transposition is weakly continuous on
    the actual duals, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem distribution_target_transpose_continuous:
  open_family_continuous (@continuous_real_dual_weak_opens R TF OF hOF)
    (@continuous_real_dual_weak_opens R TE OE hOE) distribution_target_transpose.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.
End DistributionTargetTranspose.
