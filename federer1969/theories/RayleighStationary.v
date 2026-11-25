(** Federer (1969), 1.7.3, p. 29: the stationary conclusion at a constrained
    maximum. We use the same maximum and a positive-semidefinite defect form
    instead. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm TensorUP ModuleQuotient
  BilinearDifference SemidefiniteRestriction RayleighSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rayleigh_stationary_in_subspace]: Federer 1.7.3,
    p. 29, supporting stationary identity: at a unit maximiser x
    on W, S(x,y)=S(x,x)B(x,y) for all y in W. In particular the
    mixed value vanishes if y is orthogonal to x. *)
Theorem rayleigh_stationary_in_subspace (R : rcfType) (V : lmodType R)
    (B S : V -> V -> R) (hB : is_inner_product B)
    (hS : @bilinear R V V R^o S) (hs : forall x y, S x y = S y x)
    (W : subspace V) x : W x -> inner_norm hB x = 1 ->
  (forall z, W z -> inner_norm hB z = 1 -> S z z <= S x x) ->
  forall y, W y -> S x y = S x x * B x y.
Proof.
move=> hx hnorm hm y hy.
pose T := bilinear_difference B S (S x x).
have hT : @bilinear R V V R^o T := @bilinear_differenceP R V B S (S x x) (inner_bilinear hB) hS.
have hTs : forall u v, T u v = T v u :=
  @bilinear_difference_symmetric R V B S (S x x) (inner_symmetric hB) hs.
have hp z : W z -> 0 <= T z z.
  move=> hz; rewrite /T /bilinear_difference subr_ge0.
  exact: (@quadratic_unit_bound_in_subspace R V B S hB hS W (S x x) hm z hz).
have hz : T x x = 0.
  by rewrite /T /bilinear_difference -(inner_norm_sqr hB x) hnorm expr1n mulr1 subrr.
have hh := @semidefinite_zero_diagonal_in_subspace R V T hT W hTs hp x y hx hy hz.
apply/eqP; rewrite eq_sym -subr_eq0; apply/eqP; exact hh.
Qed.
