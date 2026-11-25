(** Federer (1969), 4.1.7, pp. 355–356: fixed
    bounded linear coefficient operations are continuous
    on the original smooth-function spaces. Exact
    derivative seminorm bounds prove continuity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP DirectedSeminormFamilyUP SeminormFamilyLinearContinuity
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSeminormFamily
  SmoothFunctionTopology SmoothTargetOperatorUP SmoothTargetOperatorSeminormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SmoothTargetContinuity.
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
Variable P:Hom E F.
Hypothesis hP:is_smooth_target_operator U ev fv L P.
Local Notation I := (nat*smooth_compact_set hNX U)%type.
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation mu := (smooth_function_derivative_seminorm hG).
Local Notation p := (fun z:I=>nu z.2 z.1).
Local Notation q := (fun z:I=>mu z.2 z.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).

(** Source for [smooth_target_operator_continuous]:
    coefficient-linear smooth operators are continuous
    for the original E topologies, supporting Federer
    4.1.7, pp. 355–356. *)
Theorem smooth_target_operator_continuous:
  open_family_continuous (smooth_function_opens hD) (smooth_function_opens hG) P.
Proof.
apply:(@seminorm_family_bounded_linear_continuous R E F I I p q
  (smooth_function_opens hD) (smooth_function_opens hG) hp
  (smooth_function_topology_laws hD) (smooth_function_topology_laws hG) P).
move=>[i K].
have [C [hC hb]]:=@smooth_target_operator_seminorm_bound R X Y Z NX NY NZ
  hNX hNY hNZ U E F ev fv hE hF D G hD hG L hL P hP K i
  (nu K i) (mu K i) (smooth_function_derivative_seminorm_laws hD K i)
  (smooth_function_derivative_seminorm_laws hG K i).
exists (i,K),C; by split.
Qed.
End SmoothTargetContinuity.
