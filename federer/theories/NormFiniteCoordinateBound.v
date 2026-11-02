(** Federer (1969), 3.1.24, p. 240: a small
    sum of absolute coordinates lies in the norm neighbourhood
    on which the analytic Taylor expansion represents the function. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_finite_unit_coordinate_bound]: supporting
    the coordinate convergence region in Federer 3.1.24,
    p. 240. In a unit-norm finite vector family, the
    norm of a linear combination is at most the sum of
    the absolute coefficients. No basis or finite ambient
    dimension assumption is needed for this inequality. *)
Lemma norm_finite_unit_coordinate_bound (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_seminorm NX) n
    (v:'I_n->X) (hv:forall i,NX (v i)<=1) (t:'I_n->R) :
  NX (\sum_i t i*:v i)<=\sum_i `|t i|.
Proof.
apply:le_trans (real_seminorm_sum hNX _) _.
apply:ler_sum=>i _.
rewrite (real_seminorm_scale hNX).
have hh:=ler_wpM2l (normr_ge0 (t i)) (hv i).
by rewrite mulr1 in hh.
Qed.
