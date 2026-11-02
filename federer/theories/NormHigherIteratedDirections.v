(** Federer (1969), 3.1.11, p. 223: k-fold
    differentiability gives the recursively defined ordered partial
    derivatives, evaluated on the reversed list of directions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormTaylorLineValues ContinuousMultilinearUP ContinuousMultilinearEvaluationBound
  NormHigherDifferentialUP MultilinearSuccessorArguments
  NormIteratedDirectionalUP NormIteratedDirectionalLaws NormDifferentialLine
  IteratedDirectionalArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_iterated_directions]:
    D_(v1,...,vk)f(a) is D^k f(a) evaluated on
    (v_k,...,v_1), generalizing the coordinate formula of
    Federer 3.1.11, p. 223. Only k-fold differentiability
    at a is assumed. Domains of intermediate derivatives are
    their exact recursive domains, not additional open-set hypotheses. *)
Theorem norm_higher_differential_iterated_directions (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) (s : seq X) a (z : Z (size s)) :
  has_norm_higher_differential NX ev ZN A f (size s) a z ->
  has_norm_iterated_directional NY A f s a
    (@ev (size s) (iterated_directional_arguments s) z).
Proof.
elim:s a z=>[|v s ih] a z /=.
- by move=>[ha he]; split.
- move=>[g [hg [L [hL heL]]]].
  pose D x := exists w, has_norm_higher_differential NX ev ZN A f (size s) x w.
  pose G x := @ev (size s) (iterated_directional_arguments s) (g x).
  have hbound := continuous_multilinear_evaluation_bounded hNX (@hZ (size s))
    (iterated_directional_arguments s).
  have hDG := norm_differential_postcompose hNX hL hbound.
  have hGline := norm_differential_line hNX hNY hDG v.
  have [q hq] := @norm_iterated_directional_representative_exists R X Y NY hNY A f s.
  have [r [hr hD]] := norm_differential_interior hL.
  have [d [hd hb]] := norm_scalar_line_small_increments hNX v hr.
  have hline t (ht : `|t|<d) : D (a+t*:v) := hD _ (hb t ht).
  have hdom : norm_line_domain
      (fun x=>exists y, has_norm_iterated_directional NY A f s x y) a v.
    exists d; split=> // t ht.
    have [w hw] := hline t ht.
    exists (@ev (size s) (iterated_directional_arguments s) w).
    exact: ih _ _ hw.
  have hsame t (ht : `|t|<d) : G (a+t*:v)=q (a+t*:v).
    have [w hw] := hline t ht.
    rewrite /G (hg _ _ hw).
    symmetry; exact: hq _ _ (ih _ _ hw).
  have hqline := norm_line_derivative_local_agreement hd hsame hdom hGline.
  exists q; split; first exact hq.
  by rewrite hom_compE heL in hqline.
Qed.
