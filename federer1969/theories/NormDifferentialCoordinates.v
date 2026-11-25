(** Federer (1969), 3.1.1(5), p. 210: a map into a finite-dimensional
    normed space is differentiable exactly when its scalar components
    in a basis of the dual are differentiable. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP LinearBasis FiniteDualDimension
  Annihilator NormDifferentialUP NormFiniteLinearBound NormDifferentiableFiniteSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_coordinate_criterion]: Federer
    3.1.1(5), p. 210. The dual basis is arbitrary, not required to be
    orthonormal. The interior qualification makes the statement valid
    also for a zero-dimensional target, when the list of tests is empty.
    Finite-dimensional continuity of all coordinate maps is proved. *)
Theorem norm_differential_coordinate_criterion (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) (a : X)
    n (b : 'I_n -> Y) (hb : is_basis b)
    m (w : 'I_m -> Hom Y R^o) (hw : is_basis w) :
  norm_differentiable_at NX NY A f a <->
  norm_domain_interior NX A a /\
    forall i, norm_differentiable_at NX (fun t : R^o => `|t|) A (fun x => w i (f x)) a.
Proof.
split.
- move=> hf; split; first by have [L hL] := hf; exact: norm_differential_interior hL.
  move=> i; apply: (norm_differentiable_postcompose hNX hf).
  exact: (norm_finite_linear_bounded hNY (@scalar_absolute_value_norm R) hb (w i)).
- move=> [ha hf].
  have hc : forall j, norm_differentiable_at NX (fun t : R^o => `|t|) A
      (fun x => dual_basis hb j (f x)) a.
    move=> j.
    have hs := @norm_differentiable_scalar_linear_combination R X NX hNX A a
      (Finite.clone 'I_m _) (fun i x => w i (f x))
      (fun i => dual_basis hw i (dual_basis hb j)) ha hf.
    apply: (@norm_differentiable_agreement R X R^o NX (fun t : R^o => `|t|) hNX A
      (fun x => \sum_i dual_basis hw i (dual_basis hb j)*w i (f x))
      (fun x => dual_basis hb j (f x)) a _ hs)=> x _.
    have he := basis_vector_expansion hw (dual_basis hb j).
    rewrite {2}he.
    elim/big_rec2: _=> [|i y F _ ih]; first reflexivity.
    by rewrite hom_addE hom_scaleE -ih.
  have hs : norm_differentiable_at NX NY A
      (fun x => \sum_j (dual_basis hb j (f x) : R) *: b j) a.
    apply: (norm_differentiable_finite_pointwise_sum hNX hNY ha)=> j.
    exact: (norm_differentiable_scalar_vector hNX hNY (b j) (hc j)).
  apply: (@norm_differentiable_agreement R X Y NX NY hNX A
    (fun x => \sum_j (dual_basis hb j (f x) : R) *: b j) f a _ hs)=> x _.
  exact: esym (basis_vector_expansion hb (f x)).
Qed.

(** Source for [norm_differential_nonempty_coordinate_criterion]: the
    unqualified coordinate equivalence in Federer 3.1.1(5), p. 210,
    when the dual basis is nonempty. The first scalar differential then
    already supplies the required interior-domain condition. *)
Corollary norm_differential_nonempty_coordinate_criterion (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X)
    n (b : 'I_n -> Y) (hb : is_basis b)
    m (w : 'I_m.+1 -> Hom Y R^o) (hw : is_basis w) :
  norm_differentiable_at NX NY A f a <->
  forall i, norm_differentiable_at NX (fun t : R^o => `|t|) A (fun x => w i (f x)) a.
Proof.
have he := @norm_differential_coordinate_criterion R X Y NX NY hNX hNY A f a
  n b hb m.+1 w hw.
split.
- move=> hf; exact: (proj1 he hf).2.
- move=> hf; apply: (proj2 he); split=> //.
  have [L hL] := hf ord0; exact: norm_differential_interior hL.
Qed.
