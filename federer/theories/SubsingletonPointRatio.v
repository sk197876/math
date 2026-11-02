(** Original partial density in a local counterexample to Federer (1969),
    2.10.17(2), p. 179. A unit point mass at a has ratio one on every
    related positive-cost set and no ratio on the free singleton. This is
    the partial arithmetic of 2.1.1, p. 51, not the corrected density
    convention. the local cost differs from that example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureRestriction PointMassMeasure MeasureDerivates
  ExtendedRealConventions SubsingletonCoverCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subsingleton_point_ratio]: original partial
    quotient of a point-mass restriction and the local
    cost, for the counterexample to 2.10.17(2),
    p. 179. It uses the unmodified 2.9.1 quotient. *)
Definition subsingleton_point_ratio (R : realType) (X : choiceType) (a : X) :=
  measure_ratio_function (measure_restrict (point_mass R a) [set a]) (@subsingleton_cover_cost R X).

(** Source for [subsingleton_point_ratio_one]: supporting
    exact quotient one on positive-cost related sets
    in the local counterexample to 2.10.17(2), p. 179. *)
Lemma subsingleton_point_ratio_one (R : realType) (X : choiceType) (a : X) (S : set X) :
  S a -> subsingleton_cover_cost R S= 1 -> partial_function_graph (subsingleton_point_ratio R a) S 1.
Proof.
move=> hS hc.
have hp : 0<subsingleton_cover_cost R S by rewrite hc lte_fin ltr01.
have hf : subsingleton_cover_cost R S \is a fin_num by rewrite hc.
have hh := @measure_ratio_positive_finite_denominator R X
  (measure_restrict (point_mass R a) [set a]) (@subsingleton_cover_cost R X) S hp hf.
have hn : measure_restrict (point_mass R a) [set a] S= 1.
  apply: point_mass_in; by split.
have he : ((1 : \bar R)/1) = 1 by rewrite inver oner_eq0 invr1 mule1.
by rewrite hn hc he in hh.
Qed.

(** Source for [subsingleton_point_ratio_value]: supporting
    uniqueness of the defined density value in the
    local counterexample to 2.10.17(2), p. 179.
    A zero denominator remains undefined. *)
Lemma subsingleton_point_ratio_value (R : realType) (X : choiceType) (a : X) (S : set X) y :
  S a -> partial_function_graph (subsingleton_point_ratio R a) S y -> y= 1.
Proof.
move=> hS hy.
case: (eqVneq (subsingleton_cover_cost R S) 0)=> [hz|hne].
- have hnone := @measure_ratio_zero_denominator R X
    (measure_restrict (point_mass R a) [set a]) (@subsingleton_cover_cost R X) S hz.
  exfalso; apply: hnone; by exists y.
- have hc := subsingleton_cover_cost_nonzero hne.
  exact: partial_function_single_valued hy (subsingleton_point_ratio_one hS hc).
Qed.

(** Source for [subsingleton_point_ratio_singleton_undefined]:
    supporting missing zero-cost singleton value in the
    original quotient for 2.10.17(2), p. 179.
    The corrected density would instead be infinity. *)
Lemma subsingleton_point_ratio_singleton_undefined (R : realType) (X : choiceType) (a : X) :
  ~partial_function_domain (subsingleton_point_ratio R a) [set a].
Proof.
exact: measure_ratio_zero_denominator (subsingleton_cover_cost_singleton R a).
Qed.
