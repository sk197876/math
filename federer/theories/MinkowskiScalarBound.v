(** Federer (1969), 2.4.15, proof p. 89: the pointwise powered-norm
    comparison and cancellation after the two Holder applications. These
    supporting scalar arguments explicitly include a zero norm of f+g. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_sum_holder_factor_bound]: the third proof display of
    Federer 2.4.15, p. 89 The norm triangle law is multiplied by
    |f+g|^(p-1). *)
Lemma norm_sum_holder_factor_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (p : R) (x y : V) :
  1 < p -> real_power (N (x+y)) p <=
    N x*real_power (N (x+y)) (p-1)+N y*real_power (N (x+y)) (p-1).
Proof.
move=> hp; have hr : 0 < p-1 by rewrite subr_gt0.
have hid : real_power (N (x+y)) p = real_power (N (x+y)) (p-1) * N (x+y).
  have h := @real_power_positive_successor R (N (x+y)) (p-1) (real_seminorm_nonnegative hN.1 _) hr.
  by rewrite subrK in h.
rewrite hid mulrC -mulrDl.
apply: ler_wpM2r; first exact: real_power_nonnegative.
exact (@real_seminorm_triangle R V N hN.1 x y).
Qed.

(** Source for [minkowski_power_bound_cancel]: cancellation after the two
    Holder estimates in Federer 2.4.15, p. 89 The zero case is handled
    without dividing, and a positive power is cancelled only for a positive
    base. *)
Lemma minkowski_power_bound_cancel (R : realType) (p x a : R) :
  1 < p -> 0 <= x -> 0 <= a ->
  real_power x p <= a*real_power x (p-1) -> x <= a.
Proof.
move=> hp hx ha hb; have [->|hx0] := eqVneq x 0; first exact ha.
have hxp : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
have hr : 0 < p-1 by rewrite subr_gt0.
have hcoef := @real_power_strictly_positive R x (p-1) hxp.
have hid : real_power x p = x * real_power x (p-1).
  have h := @real_power_positive_successor R x (p-1) hx hr.
  rewrite subrK in h; by rewrite h mulrC.
by move: hb; rewrite hid ler_pM2r.
Qed.
