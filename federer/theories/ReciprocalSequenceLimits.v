(** Supporting elementary limits for Federer (1969), 2.6.3(2), p. 118 The
    Archimedean estimate already proved for the Riemann partitions implies
    convergence of 1/(n+1) to zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealErrorOrderLimit RealScalarOrderLimits
  StieltjesIntegral RationalFubiniKernel RationalPrimitiveBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reciprocal_natural_error_limit]: supporting error criterion
    for the limits in Federer 2.6.3(2), p. 118 A real sequence bounded in
    absolute value by 1/(n+1) converges to zero in the extended-real order
    topology. *)
Lemma reciprocal_natural_error_limit (R : realType) (u : nat -> R) :
  (forall n, `|u n| <= (n.+1%:R)^-1) ->
  extended_order_limit (fun n => (u n)%:E) 0%E.
Proof.
move=> hb; apply: real_error_extended_order_limit=> e he.
have [N hN] := @uniform_mesh_small R 0 1 e ler01 he.
exists N=> n hn; rewrite subr0.
apply: le_lt_trans (hb n) _.
have hh := hN n hn; by rewrite subr0 mul1r in hh.
Qed.

(** Source for [reciprocal_natural_order_limit]: the reciprocal limit used
    to evaluate integral_1^infinity x^-2 dx in Federer 2.6.3(2), p. 118 *)
Lemma reciprocal_natural_order_limit (R : realType) :
  extended_order_limit (fun n : nat => ((n.+1%:R : R)^-1)%:E) 0%E.
Proof.
apply: reciprocal_natural_error_limit=> n.
by rewrite ger0_norm ?lexx // invr_ge0 ler0n.
Qed.

(** Source for [rational_first_primitive_order_limit]: the zero limit of
    (a^2-a*y)/(a+y)^3 in Federer 2.6.3(2), p. 118, along a=n+1 This is the
    scalar endpoint limit, separate from passage of the limit through the
    actual integral. *)
Lemma rational_first_primitive_order_limit (R : realType) (y : R) :
  0 < y -> extended_order_limit
    (fun n : nat => (rational_first_primitive y n.+1%:R)%:E) 0%E.
Proof.
move=> hy; apply: reciprocal_natural_error_limit=> n.
apply: rational_first_primitive_bound=> //; by rewrite ltr0n.
Qed.
