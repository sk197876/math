(** Existential forms of finite linear calculus supporting
    Federer (1969), 3.1.1(5), p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp functions.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialFiniteCalculus NormDifferentialArithmetic NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differentiable_agreement]: representation
    independence for the coordinate criterion, Federer 3.1.1(5), p. 210.
    Equality on the domain suffices to transfer differentiability. *)
Lemma norm_differentiable_agreement (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (A : X -> Prop) (f g : X -> Y) a :
  (forall x, A x -> f x = g x) -> norm_differentiable_at NX NY A f a ->
  norm_differentiable_at NX NY A g a.
Proof.
move=> he [L hL]; exists L; exact: (@norm_differential_domain_agreement R X Y NX NY hNX A f g a L he hL).
Qed.

(** Source for [norm_differentiable_postcompose]: continuous linear
    scalarisation in Federer 3.1.1(5), p. 210, in existence form. *)
Lemma norm_differentiable_postcompose (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (A : X -> Prop) (f : X -> Y)
    (a : X) (M : Hom Y Z) :
  norm_differentiable_at NX NY A f a -> norm_bounded_linear NY NZ M ->
  norm_differentiable_at NX NZ A (fun x => M (f x)) a.
Proof.
move=> [L hL] hM; exists (hom_comp M L).
exact: (@norm_differential_postcompose R X Y Z NX NY NZ hNX A f a L M hL hM).
Qed.

(** Source for [norm_differentiable_scalar_vector]: multiplying a
    scalar coordinate function by a fixed vector in the reconstruction
    argument of Federer 3.1.1(5), p. 210. *)
Lemma norm_differentiable_scalar_vector (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> R) a (v : Y) :
  norm_differentiable_at NX (fun t : R^o => `|t|) A f a ->
  norm_differentiable_at NX NY A (fun x => f x *: v) a.
Proof.
move=> hf.
have hlin : linear (fun t : R^o => t *: v).
  by move=> c s t; rewrite scalerDl scalerA.
pose M := @HomMap R R^o Y (fun t => t *: v) (introT (asboolP _) hlin).
apply: (@norm_differentiable_postcompose R X R^o Y NX
  (fun t : R^o => `|t|) NY hNX A f a M hf).
exists (NY v); split; first exact: real_seminorm_nonnegative hNY.1 v.
by move=> t; change (NY (t *: v) <= NY v * `|t|);
  rewrite (real_seminorm_scale hNY.1) mulrC.
Qed.

(** Source for [norm_differentiable_finite_pointwise_sum]: finite
    sums of differentiable coordinate functions in Federer 3.1.1(5),
    p. 210. An interior domain point is retained for an empty sum. *)
Lemma norm_differentiable_finite_pointwise_sum (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (a : X)
    (I : finType) (f : I -> X -> Y) :
  norm_domain_interior NX A a ->
  (forall i, norm_differentiable_at NX NY A (f i) a) ->
  norm_differentiable_at NX NY A (fun x => \sum_i f i x) a.
Proof.
move=> ha hf.
have hs := norm_differentiable_finite_sum hNX hNY ha hf.
apply: (@norm_differentiable_agreement R X Y NX NY hNX A (\sum_i f i)
  (fun x => \sum_i f i x) a _ hs)=> x _.
by elim/big_rec2: _=> [|i y g _ <-].
Qed.

(** Source for [norm_differentiable_scalar_linear_combination]: finite
    linear combinations of scalar coordinates in Federer 3.1.1(5), p. 210.
    This allows testing any supplied dual basis, not just a fixed one. *)
Lemma norm_differentiable_scalar_linear_combination (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (A : X -> Prop) (a : X)
    (I : finType) (f : I -> X -> R) (c : I -> R) :
  norm_domain_interior NX A a ->
  (forall i, norm_differentiable_at NX (fun t : R^o => `|t|) A (f i) a) ->
  norm_differentiable_at NX (fun t : R^o => `|t|) A
    (fun x => \sum_i c i*f i x) a.
Proof.
move=> ha hf; apply: (norm_differentiable_finite_pointwise_sum hNX
  (@scalar_absolute_value_norm R) ha)=> i.
have [L hL] := hf i; exists (c i *: L).
exact: (@norm_differential_scale R X R^o NX (fun t : R^o => `|t|)
  hNX (@scalar_absolute_value_norm R) A (f i) a L (c i) hL).
Qed.
