(** Federer (1969), 4.1.1, p. 344: the exact finite
    derivative-seminorm criterion for a continuous real linear
    functional on E(U,Y). This specializes the already proved
    directed-seminorm mapping criterion to the scalar norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed OpenFamilyTopologyUP
  DirectedSeminormFamilyUP NormOpenTopology SeminormFamilyLinearContinuity
  SmoothCompactSet SmoothFunctionDerivativesUP SmoothFunctionSeminormFamily SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothDualBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation I := (nat * smooth_compact_set hNX U)%type.
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation p := (fun z:I=>nu z.2 z.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).
Local Notation EO := (smooth_function_opens hD).
Local Notation RO := (norm_open_family (@scalar_absolute_value_norm R)).

(** Source for [smooth_dual_finite_bound]: a real linear
    functional is continuous exactly when some M nu^i_K
    bounds its absolute value on every smooth function,
    Federer 4.1.1, p. 344. The bound includes K empty. *)
Theorem smooth_dual_finite_bound (L:Hom E R^o):
  open_family_continuous EO RO L <->
  exists (i:nat) (K:smooth_compact_set hNX U) (C:R),0<=C /\
    forall f,`|L f|<=C * nu K i f.
Proof.
have hR:=@norm_open_family_seminorm_laws R R^o (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R).
have hRI:=@norm_single_seminorm_directed R R^o (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R).
split.
- move=>hL.
  have [[i K] [C [hC hb]]]:=@seminorm_family_continuous_linear_bound R E R^o I unit
    p (fun (_:unit) (t:R^o)=>`|t|) EO RO hp hRI (smooth_function_topology_laws hD) hR L hL tt.
  by exists i,K,C.
- move=>[i [K [C [hC hb]]]].
  apply:(@seminorm_family_bounded_linear_continuous R E R^o I unit p
    (fun (_:unit) (t:R^o)=>`|t|) EO RO hp (smooth_function_topology_laws hD) hR L)=>j.
  by exists (i,K),C.
Qed.
End SmoothDualBound.
