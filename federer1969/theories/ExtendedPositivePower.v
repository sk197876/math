(** Federer (1969), 2.4.12, pp. 86–87: positive powers and roots of
    nonnegative extended numbers in the Lp formula. Only positive exponents
    and nonnegative arguments are specified; the negative-infinity branch is
    an arbitrary totalisation outside that mathematical domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_power]: scalar positive-power
    convention for the possibly infinite integral in Federer
    2.4.12, p. 86. Positive infinity stays infinite. *)
Definition extended_positive_power (R : realType) (x : \bar R) (p : R) : \bar R :=
  match x with EFin r => (real_power r p)%:E | +oo => +oo | -oo => 0 end.

(** Source for [extended_positive_power_nonnegative]: scalar
    sign of the power in Federer 2.4.12, p. 86. *)
Lemma extended_positive_power_nonnegative (R : realType) (x : \bar R) (p : R) :
  0 <= extended_positive_power x p.
Proof. by case: x=> [x| |] /=; rewrite /extended_positive_power ?lee_fin ?real_power_nonnegative ?leey ?lexx. Qed.

(** Source for [extended_positive_power_zero]: positive powers
    of zero in the Lp definition, Federer 2.4.12, p. 86. *)
Lemma extended_positive_power_zero (R : realType) (p : R) :
  (0 < p)%R -> extended_positive_power 0 p = 0.
Proof. by move=> hp; rewrite /extended_positive_power /= real_power_zero_base ?gt_eqF. Qed.

(** Source for [extended_positive_power_one]: p = 1 scalar
    specialisation of Federer 2.4.12, p. 86. *)
Lemma extended_positive_power_one (R : realType) (x : \bar R) :
  0 <= x -> extended_positive_power x 1%R = x.
Proof. case: x=> [x| |] //=; rewrite lee_fin=> hx; by rewrite real_power_one_exponent. Qed.

(** Source for [extended_positive_power_finite_iff]: finiteness
    of a positive power is equivalent to finiteness of its
    nonnegative argument, supporting Federer 2.4.12, p. 86. *)
Lemma extended_positive_power_finite_iff (R : realType) (x : \bar R) (p : R) :
  0 <= x -> (0 < p)%R ->
  (extended_positive_power x p < +oo) = (x < +oo).
Proof. by case: x=> [x| |] /=; rewrite ?ltry ?ltxx ?leeNy_eq ?eqxx. Qed.

(** Source for [extended_positive_power_monotone]: order
    preservation supporting the Lp comparisons in Federer
    2.4.12, pp. 86–87. *)
Lemma extended_positive_power_monotone (R : realType) (x y : \bar R) (p : R) :
  0 <= x -> x <= y -> (0 < p)%R ->
  extended_positive_power x p <= extended_positive_power y p.
Proof.
case: x=> [x| |]; case: y=> [y| |] /=; rewrite ?leey //=.
rewrite !lee_fin=> hx hxy hp; exact: real_power_monotone hx hxy hp.
Qed.

(** Source for [extended_positive_power_root_cancel]: cancellation
    of the positive root in Federer 2.4.12, p. 86,
    including zero and positive infinity. *)
Lemma extended_positive_power_root_cancel (R : realType) (x : \bar R) (p : R) :
  0 <= x -> (0 < p)%R ->
  extended_positive_power (extended_positive_power x p) p^-1 = x.
Proof.
case: x=> [x| |] //=; rewrite lee_fin=> hx hp.
by rewrite real_power_root_cancel.
Qed.
