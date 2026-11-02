(** Federer (1969), 3.1.1, p. 211: supporting norm estimates
    for the closed remainder tests in the Borel graph argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormMetricContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_difference_difference_bound]: the triangle
    bound for two differences, supporting continuity of the
    differential remainder in 3.1.1, p. 211. *)
Lemma norm_difference_difference_bound (R : realType) (Y : lmodType R)
    (N : Y -> R) (hN : is_real_norm N) (u v u' v' : Y) :
  N ((u-v)-(u'-v'))<=N (u-u')+N (v-v').
Proof.
have -> : (u-v)-(u'-v')=(u-u')-(v-v') by rewrite !opprD opprK addrACA.
apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
by rewrite (real_seminorm_negate hN.1).
Qed.

(** Source for [norm_remainder_variation_bound]: supporting
    three-term continuity estimate for the remainder used in
    3.1.1, p. 211. It applies to arbitrary normed targets. *)
Lemma norm_remainder_variation_bound (R : realType) (Y : lmodType R)
    (N : Y -> R) (hN : is_real_norm N) (u v w u' v' w' : Y) :
  N (u-v-w)-N (u'-v'-w')<=N (u-u')+N (v-v')+N (w-w').
Proof.
apply: le_trans (real_norm_difference_bound hN _ _) _.
apply: le_trans (norm_difference_difference_bound hN _ _ _ _) _.
exact: lerD (norm_difference_difference_bound hN _ _ _ _) (lexx _).
Qed.
