(** Federer (1969), 2.3.8, p. 78: the characteristic formula for the whole
    source, used in the examples showing failure of homogeneity and
    convexity. Source context: MeasureGaugeCharacteristic.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionBasic MeasureUP MeasureGauge MeasureGaugeCharacteristic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_gauge_total_constant]: whole-source
    special case of the formula in Federer 2.3.8, p. 78:
    the gauge of a constant vector is min(its norm,mu(X)). *)
Lemma measure_gauge_total_constant (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R) (y : Y) :
  (0 <= N y)%R -> measure_gauge mu N (partial_function_total (fun _ : X => y)) =
    Order.min (N y)%:E (mu setT).
Proof.
move=> hy; apply: (@measure_gauge_two_value_norm R X Y mu hm N (fun _ => y) setT (N y) hy).
- by move=> x hx.
- by move=> x hn; exfalso; apply: hn.
Qed.
