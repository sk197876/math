(** Federer (1969), 3.1.11, pp. 219–220:
    identities in the arguments of lower differentials
    persist when one more differential is taken.
    This gives the inherited part of higher symmetry. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialDirectional NormDifferentialFiniteCalculus
  ContinuousMultilinearUP ContinuousMultilinearEvaluationBound
  NormHigherDifferentialUP MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_inherit_argument_identity]:
    the induction step for symmetry of higher
    differentials in Federer 3.1.11, p. 220.
    If two argument evaluations agree at every
    point of the exact lower-differential domain,
    their derivatives agree at the next order. *)
Theorem norm_higher_differential_inherit_argument_identity (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall j, {ffun 'I_j->X}->Hom (Z j) Y)
    (ZN : forall j, Z j->R)
    (hZ : forall j, is_continuous_multilinear_space NX NY (@ez j) (@ZN j))
    (A : X->Prop) (f : X->Y) a (z : Z k.+1)
    (u v : {ffun 'I_k->X}) :
  (forall x w, has_norm_higher_differential NX ez ZN A f k x w ->
    @ez k u w=@ez k v w) ->
  has_norm_higher_differential NX ez ZN A f k.+1 a z ->
  forall t, @ez k.+1 (multilinear_successor_arguments u t) z=
    @ez k.+1 (multilinear_successor_arguments v t) z.
Proof.
move=> heval [g [hg [L [hL he]]]] t.
have hbu := continuous_multilinear_evaluation_bounded hNX (@hZ k) u.
have hbv := continuous_multilinear_evaluation_bounded hNX (@hZ k) v.
have hDu := norm_differential_postcompose hNX hL hbu.
have hDv := norm_differential_postcompose hNX hL hbv.
have hsame x : (exists w, has_norm_higher_differential NX ez ZN A f k x w) ->
    @ez k u (g x)=@ez k v (g x).
  move=> [w hw]; rewrite (hg x w hw); exact: heval x w hw.
have hDu' := norm_differential_domain_agreement hNX hsame hDu.
have hmaps := norm_differential_unique hNX hNY hDu' hDv.
have hh := congr1 (fun M : Hom X Y=>M t) hmaps.
by rewrite !hom_compE !he in hh.
Qed.
