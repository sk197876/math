(** Federer (1969), 2.4.15, p. 89: conversion of the printed norm
    proportions into vector proportions for an inner-product norm. it has no
    integration analogue. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP InnerProductUP InnerNormUP InnerTriangleEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_norm_proportions_multiple]: supporting pointwise
    implication for Federer 2.4.15, p. 89. The global norm
    coefficients a,b determine the same vector coefficient a/b at every
    point when b is positive, including points where both vectors vanish. *)
Lemma inner_norm_proportions_multiple (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) (hBN : is_inner_norm B N)
    (a b : R) (x y : V) :
  0 < b -> a+b = 1 -> N x=a*N (x+y) -> N y=b*N (x+y) -> x=(a/b) *: y.
Proof.
move=> hb hab hx hy.
have hb0 : b != 0 by rewrite gt_eqF.
have hny : N (x+y)=b^-1*N y by rewrite hy mulrA mulVf // mul1r.
have hxy : N x=(a/b)*N y by rewrite hx hny mulrA.
have [hy0|hy0] := eqVneq y 0.
- have hx0 : x=0 by apply: hN.2; rewrite hxy hy0 (real_seminorm_zero hN.1) mulr0.
  by rewrite hx0 hy0 scaler0.
have he : N (x+y)=N x+N y by rewrite hx hy -mulrDl hab mul1r.
have [t [ht htx]] := @inner_triangle_positive_multiple R V B hB N hN hBN x y hy0 he.
have hny0 : N y != 0 by rewrite (real_norm_zero_test hN.1 hN.2).
have htN : t*N y=(a/b)*N y.
  by rewrite -hxy htx (real_seminorm_scale hN.1) (ger0_norm ht).
have htval : t=a/b by apply: (mulIf hny0); exact htN.
by rewrite htx htval.
Qed.
