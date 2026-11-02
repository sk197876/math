(** Federer (1969), proof of 2.5.2, p. 93: application of 2.4.7 to the
    positive lattice approximants. This adapter supplies the integral
    witnesses from their abstract lower-integral laws; values may be
    infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverMeasure DaniellPositiveIntegral RealTotalCharacteristicBounds
  SummableRealFunctionUP RealTotalIntegralLimits ExtendedRealOrderLimit PartialFunctionLimitExtremaUP
  MeasureIncreasingConvergence MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_positive_increasing_integral_values]: increasing
    integral limits in the last paragraph of Federer 2.5.2, p. 93 *)
Lemma daniell_positive_increasing_integral_values (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : nat -> X -> R) (g : X -> R) :
  (forall n, positive_function_lattice L (f n)) -> positive_function_lattice L g ->
  real_functions_increase_to f g ->
  extended_increases_to (fun n => measure_lower_integral mu (real_total_integrand (f n)))
    (measure_lower_integral mu (real_total_integrand g)).
Proof.
move=> hf hg hinc.
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hg.1).
have hl : is_partial_function_lower_limit (fun n => real_total_integrand (f n)) (real_total_integrand g).
  apply: real_total_pointwise_lower_limit=> x; exact: (hinc x).2.
apply: (@measure_increasing_integral_values R X mu hmeasure
  (fun n => real_total_integrand (f n)) (real_total_integrand g)
  (fun n => measure_lower_integral mu (real_total_integrand (f n)))
  (measure_lower_integral mu (real_total_integrand g)) hl).
- move=> n; exact: (@real_total_nonnegative_almost R X mu hmeasure (f n) (hf n).2).
- move=> n; apply: (@real_total_pointwise_order_almost R X mu hmeasure (f n) (f n.+1))=> x.
  have hh := (hinc x).1 n n.+1 (leqnSn n); by move: hh; rewrite lee_fin.
- move=> n; exact: (daniell_positive_lattice_integral hL hA hm (hf n)).1.
- exact: (daniell_positive_lattice_integral hL hA hm hg).1.
Qed.
