(** Existence proof for the nonnegative extended-input norm formulas used in
    Federer (1969), 2.10.5, p. 172, from 2.4.12, p. 86. The finite case uses
    the locally proved integrability of every nonnegative measurable
    function, 2.4.4(2), p. 82; infinity uses the abstract extended-real
    infimum. The implementation is hidden by a seal. Source context and
    scope of this extension: NonnegativeExtendedExponentNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower ExtendedRealBounds
  PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralBounds MeasureNonnegativeIntegral
  MeasurableNonnegativeExtendedPower NonnegativeExtendedExponentNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_exponent_norm_witness]:
    private witness for the two formulas applied in
    Federer 2.10.5, p. 172. The value at
    negative infinity is only an out-of-domain
    totalization; admissible exponents satisfy t>=1. *)
Definition nonnegative_extended_exponent_norm_witness (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t : \bar R) :=
  match t with
  | p%:E => extended_positive_power (measure_lower_integral mu
      (partial_function_total (fun x => extended_positive_power (f x) p))) p^-1
  | +oo => extended_real_inf (nonnegative_extended_essential_thresholds mu f)
  | -oo => 0
  end.

(** Source for [nonnegative_extended_exponent_norm_witness_laws]:
    existence for the extended projected-volume inputs
    in Federer 2.10.5, p. 172. Infinite values
    are retained by the nonnegative integral theorem
    and by the essential-bound infimum. *)
Lemma nonnegative_extended_exponent_norm_witness_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (t : \bar R) :
  (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_nonnegative_extended_exponent_norm mu f t
    (nonnegative_extended_exponent_norm_witness mu f t).
Proof.
move=> hf0 ht hf; case: t ht=> [p| |] ht //=.
- split; first by move: ht; rewrite lee_fin.
  exists (measure_lower_integral mu (partial_function_total
    (fun x => extended_positive_power (f x) p))); split=> //.
  have hp : (0<p)%R by move: ht; rewrite lee_fin=> ht; exact: lt_le_trans ltr01 ht.
  have hh := measurable_nonnegative_extended_power hm hf0 hp hf.
  apply: (nonnegative_measurable_function_integral hm hh _).1.
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (extended_positive_power (f x) p); split=> //.
  exact: extended_positive_power_nonnegative.
- split.
  - exact: extended_real_inf_lower.
  - exact: extended_real_inf_greatest.
Qed.
