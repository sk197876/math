(** Federer (1969), 3.1.24, pp. 238–239:
    smoothness and the exact higher differentials of a
    limit with uniformly convergent differential fields. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormClassOneUP InnerConvex
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherDifferentialFields
  NormClassHigherUP NormUniformLimitClassZero NormHigherFieldsUniformStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_smooth_uniform_limit]: the induction
    proving D^i f=sum_m D^i p_m in Federer 3.1.24,
    p. 239, isolated from the scalar majorant estimate.
    Uniform limits of continuous actual higher differential
    fields are continuous and satisfy the recursive differential
    laws. The order-zero field must represent the actual
    limiting function. All limits are given by proved witnesses,
    not by an assumed differentiation-of-series axiom. *)
Theorem norm_smooth_uniform_limit (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A:X->Prop) (F:nat->X->Y) (D:forall N:nat,forall i,X->Z i)
    (G:forall i,X->Z i) (f:X->Y) :
  is_inner_convex A -> norm_class_zero NX NY A f ->
  (forall N i x,A x -> has_norm_higher_differential NX ev ZN A (F N) i x (D N i x)) ->
  (forall N i,norm_class_zero NX (@ZN i) A (D N i)) ->
  (forall i,forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,A x -> @ZN i (D N i x-G i x)<eps) ->
  (forall x,A x -> has_norm_higher_differential NX ev ZN A f 0%N x (G 0%N x)) ->
  norm_class_infinity NX NY ev ZN A f /\
    forall i x,A x -> has_norm_higher_differential NX ev ZN A f i x (G i x).
Proof.
move=>hA hf hd hcD hu hG0.
have hG i:norm_class_zero NX (@ZN i) A (G i).
  exact (@norm_uniform_limit_class_zero R X (Z i) NX (@ZN i)
    (continuous_multilinear_norm_is_norm hNY (hZ i)) A (fun N=>D N i) (G i)
    (fun N=>hcD N i) (hu i)).
have hactual i:forall x,A x -> has_norm_higher_differential NX ev ZN A f i x (G i x).
  elim:i=>[|i ih]; first exact hG0.
  move=>x hx.
  have [L [hL he]]:=@norm_higher_fields_uniform_step R X Y NX NY hNX hNY Z ev ZN hZ
    A F D G i hA hd hu x hx.
  exact (@norm_higher_differential_field_step R X Y NX NY hNX hNY Z ev ZN hZ
    A f i (G i) x L (G i.+1 x) ih hL he).
split; last exact hactual.
move=>i; split; first exact hf.
exists (G i); split; [exact (hactual i)|exact (hG i)].
Qed.
