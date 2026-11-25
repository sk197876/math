(** Federer (1969), 4.1.1, p. 346: the actual smooth
    directional derivative is continuous. This proof uses the
    original defining seminorms and loses one derivative order,
    preserving the compact set in every estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP DirectedSeminormFamilyUP SeminormFamilyLinearContinuity
  SmoothCompactSet SmoothFunctionDerivativesUP SmoothFunctionSeminormFamily
  SmoothFunctionTopology SmoothDirectionalDerivativeUP SmoothDirectionalSeminormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DirectionalContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.
Local Notation I := (nat * smooth_compact_set hNX U)%type.
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation p := (fun z:I=>nu z.2 z.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).
Local Notation O := (smooth_function_opens hD).
Local Notation hO := (smooth_function_topology_laws hD).

(** Source for [smooth_directional_derivative_continuous]:
    the directional derivative is continuous on E(U,Y), supporting
    the test-function and dual differential operators of Federer
    4.1.1, p. 346. No completeness or finite target dimension
    is added to this supporting continuity proof. *)
Theorem smooth_directional_derivative_continuous:
  open_family_continuous O O P.
Proof.
apply:(@seminorm_family_bounded_linear_continuous R E E I I p p O O hp hO hO P).
move=>z; case:z=>i K.
have [C [hC hb]]:=@smooth_directional_seminorm_bound R X Y NX NY hNX hNY U hU E ev D hD
  v P hP K i (nu K i) (nu K i.+1)
  (smooth_function_derivative_seminorm_laws hD K i)
  (smooth_function_derivative_seminorm_laws hD K i.+1).
exists (i.+1,K),C; by split.
Qed.
End DirectionalContinuity.
