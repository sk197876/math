(** Triangle estimate in Federer (1969), 2.10.32, p. 197: half the
    difference of two original endpoint products has norm at most their
    common upper bound. This supporting lemma uses only the real seminorm
    laws, so positive definiteness is unnecessary. It is later applied to
    the actual exterior norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [double_difference_seminorm_bound]: supporting
    last triangle inequality in 2.10.32,
    p. 197. The estimate is independent of
    any chosen inner-product construction and
    retains zero upper bounds. *)
Lemma double_difference_seminorm_bound (R : realType) (V : lmodType R)
    (N : V -> R) (x y z : V) (M : R) :
  is_real_seminorm N -> 2*:x=y-z -> N y<=M -> N z<=M -> N x<=M.
Proof.
move=> hN he hy hz.
have hh := real_seminorm_triangle hN y (-z).
rewrite (real_seminorm_negate hN) -he (real_seminorm_scale hN) normr_nat in hh.
lra.
Qed.
