(** Federer (1969), 2.4.12, pp. 86–87: positive powers and roots of
    nonnegative extended numbers in the Lp formula. Only positive exponents
    and nonnegative arguments are specified; the negative-infinity branch is
    an arbitrary totalisation outside that mathematical domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition ExtendedRealOrderTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_power]: the partial integrand
    |f|^p in Federer 2.4.12, p. 86. Its domain is
    exactly the original domain of f. *)
Definition partial_norm_power (R : realType) (X Y : Type)
    (N : Y -> R) (p : R) (f : partial_function X Y) : partial_function X (extended_real_line R) :=
  partial_function_postcompose f (fun y => (real_power (N y) p)%:E).

(** Source for [partial_norm_power_domain]: domain preservation
    for the integrand of Federer 2.4.12, p. 86. *)
Lemma partial_norm_power_domain (R : realType) (X Y : Type)
    (N : Y -> R) (p : R) (f : partial_function X Y) :
  partial_function_domain (partial_norm_power N p f) = partial_function_domain f.
Proof. exact: partial_function_postcompose_domain. Qed.

(** Source for [partial_norm_power_almost_nonnegative]: the
    nonnegative integrand in Federer 2.4.12, p. 86,
    with the original conull-domain requirement explicit. *)
Lemma partial_norm_power_almost_nonnegative (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R) (p : R)
    (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_norm_power N p f)).
Proof.
move=> hf; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf).
move=> x [y hy]; exists (real_power (N y) p)%:E; split.
- exists y; by split.
- by rewrite lee_fin real_power_nonnegative.
Qed.
