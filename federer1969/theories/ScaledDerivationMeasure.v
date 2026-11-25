(** Federer (1969), 2.9.14, pp. 159–160: openness of the locus where one
    closed-ball measure strictly exceeds another for an allowed radius. The
    proof uses monotonicity, continuity from above in 2.1.3(5), p. 55, and
    the metric triangle inequality. no separate item there states this
    ball-comparison lemma. The working erratum has no correction to 2.9.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP
  MeasureDerivationContext FiniteMeasureScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_scaled_derivation_measure]: supporting
    class-M closure needed by both corollaries of Federer
    2.9.14, p. 160. Multiplication by a finite positive
    scalar preserves the measure law, Borel equal-mass covers,
    open-set measurability, and finiteness on bounded sets.
    These follow from 2.1.1(6) and 2.1.2, pp. 52–54. *)
Lemma positive_scaled_derivation_measure (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (t : R) :
  is_derivation_measure phi -> (0<t)%R ->
  is_derivation_measure (fun S => t%:E*phi S).
Proof.
move=> hphi ht; have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
constructor.
- exact: (@finite_scale_is_measure R X phi hm t (ltW ht)).
- constructor.
  + move=> U hU T; have hUm := @borel_regular_open_measurable R X phi hr U hU.
    rewrite (hUm T).
    exact: (@ge0_muleDr R t%:E _ _
      (@measure_nonnegative R X phi hm (T `&` U))
      (@measure_nonnegative R X phi hm (T `\` U))).
  + move=> A; have [B [hAB [hB he]]] := borel_regular_cover hr A.
    exists B; split=> //; split=> //; by rewrite he.
- move=> A hA.
  have hf : phi A \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm A)).
    exact: derivation_measure_bounded_finite hphi A hA.
  by rewrite -(fineK hf) -EFinM ltry.
Qed.
