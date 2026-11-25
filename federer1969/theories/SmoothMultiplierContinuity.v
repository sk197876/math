(** Federer (1969), 4.1.1, pp. 344–345: continuity of
    smooth scalar multiplication on E(U,Y), using the original
    compact derivative seminorms and the proved Leibniz bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity ContinuousMultilinearSealed
  OpenFamilyTopologyUP DirectedSeminormFamilyUP SeminormFamilyLinearContinuity
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSeminormFamily
  SmoothFunctionTopology SmoothMultiplierUP SmoothMultiplierSeminormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section MultiplierContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.
Variable P:Hom E E.
Hypothesis hP:is_smooth_multiplier U ev u P.
Local Notation I := (nat * smooth_compact_set hNX U)%type.
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation p := (fun z:I=>nu z.2 z.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).
Local Notation O := (smooth_function_opens hD).
Local Notation hO := (smooth_function_topology_laws hD).

(** Source for [smooth_multiplier_continuous]: phi to u phi
    is continuous in E(U,Y), supporting the compact-support
    dual and partition assertions of Federer 4.1.1,
    pp. 344–345. Arbitrary normed targets are retained. *)
Theorem smooth_multiplier_continuous:open_family_continuous O O P.
Proof.
apply:(@seminorm_family_bounded_linear_continuous R E E I I p p O O hp hO hO P).
move=>z; case:z=>i K.
have [C [hC hb]]:=@smooth_multiplier_seminorm_bound R X Y NX NY hNX hNY U hU E ev hE D hD
  u hu P hP K i (nu K i) (smooth_function_derivative_seminorm_laws hD K i).
exists (i,K),C; by split.
Qed.
End MultiplierContinuity.
