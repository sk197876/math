(** Federer (1969), 3.4.12, p. 338:
    differentiating an actual argument identity with a
    bounded target map preserves that identity at the
    next order. This is the missing target-map connection
    to the argument-identity theorem of 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialDirectional NormDifferentialFiniteCalculus
  ContinuousMultilinearUP ContinuousMultilinearEvaluationBound
  NormHigherDifferentialUP MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_argument_linear_identity]: the
    higher complex-linearity implication of 3.4.12, p. 338.
    The supporting statement allows any bounded target map;
    actual derivative uniqueness supplies the conclusion. *)
Theorem norm_higher_argument_linear_identity (R:realType) k
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R)
    (ez:forall j,{ffun 'I_j->X}->Hom (Z j) Y)
    (ZN:forall j,Z j->R)
    (hZ:forall j,is_continuous_multilinear_space NX NY (@ez j) (@ZN j))
    (M:Hom Y Y) (A:X->Prop) (f:X->Y) a (z:Z k.+1)
    (u v:{ffun 'I_k->X}):
  norm_bounded_linear NY NY M ->
  (forall x w,has_norm_higher_differential NX ez ZN A f k x w ->
    @ez k u w=M (@ez k v w)) ->
  has_norm_higher_differential NX ez ZN A f k.+1 a z ->
  forall t,@ez k.+1 (multilinear_successor_arguments u t) z=
    M (@ez k.+1 (multilinear_successor_arguments v t) z).
Proof.
move=>hM hIdentity [g [hG [L [hL hEvaluation]]]] t.
have hU:=continuous_multilinear_evaluation_bounded hNX (@hZ k) u.
have hV:=continuous_multilinear_evaluation_bounded hNX (@hZ k) v.
have hDU:=norm_differential_postcompose hNX hL hU.
have hDV:=norm_differential_postcompose hNX hL hV.
have hDMV:=norm_differential_postcompose hNX hDV hM.
have hSame x:(exists w,has_norm_higher_differential NX ez ZN A f k x w) ->
    @ez k u (g x)=M (@ez k v (g x)).
  move=>[w hw];rewrite (hG x w hw);exact:hIdentity x w hw.
have hDU':=norm_differential_domain_agreement hNX hSame hDU.
have hMaps:=norm_differential_unique hNX hNY hDU' hDMV.
have hAt:=congr1 (fun T:Hom X Y=>T t) hMaps.
by rewrite !hom_compE !hEvaluation in hAt.
Qed.
