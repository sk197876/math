(** Federer (1969), 3.1.1, p. 209: local increment bounds underlying
    the limsup and liminf formulas. These are the estimate directions;
    the sharp limiting equalities require additional arguments. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_norm_bounds]: supporting estimates
    for the two local-ratio identities in Federer 3.1.1, p. 209.
    If n is the operator norm of L and m bounds its expansion from below,
    sufficiently small increments of f lie between (m-e)|h| and
    (n+e)|h|. This statement alone does not establish sharpness. *)
Theorem norm_differential_norm_bounds (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y) (n m : R) :
  has_norm_differential NX NY A f a L ->
  is_norm_operator_norm NX NY L n ->
  (forall h, m*NX h <= NY (L h)) ->
  forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall h, A (a+h) -> NX h < d ->
      (m-e)*NX h <= NY (f (a+h)-f a) /\
      NY (f (a+h)-f a) <= (n+e)*NX h.
Proof.
move=> hf hn hm e he.
have [d [hd hr]] := norm_differential_remainder hf he.
exists d; split=> // h ha hh; have hrem := hr h ha hh.
pose k := f (a+h)-f a.
split.
- have heq : L h = k + -(k-L h) by rewrite opprB addrC subrK.
  have htri : NY (L h) <= NY k + NY (k-L h).
    rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
    by rewrite (real_seminorm_negate hNY.1).
  have hlow := le_trans (hm h) htri.
  change (is_true (NY (k-L h) <= e*NX h)) in hrem.
  change ((m-e)*NX h <= NY k); by nra.
- have heq : k = (k-L h)+L h by rewrite subrK.
  change (NY k <= (n+e)*NX h).
  rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD hrem (norm_operator_bound hn h)) _.
  by rewrite -mulrDl addrC.
Qed.
