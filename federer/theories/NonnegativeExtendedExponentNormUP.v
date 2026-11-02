(** Federer (1969), 2.10.5, p. 172, applies the formulas of 2.4.12, p. 86,
    to the nonnegative extended-valued projected-volume function. Specify
    those actual formulas before constructing a value: a root of the
    integral of the positive power for finite t, and the infimum of
    nonnegative null-superlevel bounds for infinity. This extends the
    existing finite- scalar interface, and does not assume seminorm laws on
    extended-valued functions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_essential_thresholds]:
    supporting admissible bounds in the infinity
    formula used by Federer 2.10.5, p. 172,
    from 2.4.12, p. 86. Nonnegative thresholds
    preserve the established zero-measure convention. *)
Definition nonnegative_extended_essential_thresholds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> \bar R) : set (\bar R) :=
  [set r | 0<=r /\ mu [set x | r<f x]=0].

(** Source for [is_nonnegative_extended_exponent_norm]:
    abstract integral-root and essential-bound formulas
    for the projected-volume inputs in Federer
    2.10.5, p. 172. Positive infinity is an
    allowed input and an allowed resulting value. *)
Definition is_nonnegative_extended_exponent_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t a : \bar R) : Prop :=
  match t with
  | p%:E => (1<=p)%R /\ exists b,
      is_measure_integral mu
        (partial_function_total (fun x => extended_positive_power (f x) p)) b /\
      a=extended_positive_power b p^-1
  | +oo =>
      (forall r, nonnegative_extended_essential_thresholds mu f r -> a<=r) /\
      (forall b, (forall r, nonnegative_extended_essential_thresholds mu f r -> b<=r) -> b<=a)
  | -oo => False
  end.

(** Source for [nonnegative_extended_exponent_norm_unique]:
    supporting uniqueness for the formulas in Federer
    2.10.5, p. 172: integral uniqueness at finite
    exponent and order antisymmetry at infinity. *)
Lemma nonnegative_extended_exponent_norm_unique (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t a b : \bar R) :
  is_nonnegative_extended_exponent_norm mu f t a ->
  is_nonnegative_extended_exponent_norm mu f t b -> a=b.
Proof.
case: t=> [p| |] //=.
- move=> [_ [u [hu ->]]] [_ [v [hv ->]]].
  by rewrite (measure_integral_unique hu hv).
- move=> [ha hla] [hb hlb]; apply/eqP; rewrite eq_le; apply/andP; split.
  - exact: hlb _ ha.
  - exact: hla _ hb.
Qed.

(** Source for [nonnegative_extended_exponent_norm_nonnegative]:
    supporting nonnegativity of the gauge numerator
    in Federer 2.10.5, p. 172, derived from
    the two formulas rather than postulated. *)
Lemma nonnegative_extended_exponent_norm_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t a : \bar R) :
  is_nonnegative_extended_exponent_norm mu f t a -> 0<=a.
Proof.
case: t=> [p| |] //=.
- move=> [_ [b [_ ->]]]; exact: extended_positive_power_nonnegative.
- move=> [_ h]; apply: h=> r [hr _]; exact hr.
Qed.
