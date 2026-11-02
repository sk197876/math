(** Supporting Haar parameter products in Federer (1969), 2.10.16, p. 178.
    The normalized orthogonal-group measure of 2.7.16(6), p. 139, is a Borel
    regular measure and has countably measurable whole space. These follow
    from the already proved Radon theorem 2.7.14, pp. 131–132, and
    compactness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOrthogonalInvariantMeasures InnerMetric OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation
  HaarIntegralUP HaarIntegralLaws CovariantMeasureRadon RadonMeasureUP RadonBorelRegularity
  BorelRegularMeasureUP MeasureUP MeasureSplit CountablyMeasurableUP CountablyMeasurableBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section OrthogonalProbability.
Variable R : realType.
Variable n : nat.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.

(** Source for [orthogonal_probability_is_measure]: supporting
    measure law for the theta_n parameter in 2.10.16,
    p. 178, from its existing Haar specification in
    2.7.16(6), p. 139. *)
Lemma orthogonal_probability_is_measure : is_measure theta.
Proof. by have [[Th [_ hm _ _]] _] := htheta. Qed.

(** Source for [orthogonal_probability_borel_regular]: supporting
    regular parameter measure for 2.10.16, p. 178.
    Compactness discharges the sigma-compact alternative in
    the already proved Radon theorem 2.7.14, pp. 131–132. *)
Lemma orthogonal_probability_borel_regular : is_borel_regular_measure theta.
Proof.
have hOc := @orthogonal_group_compact_space R (R_n R n) (@euclidean_inner_product R n)
  hBn n (@coordinate_basis R n) hbn.
have hrad : is_radon_measure theta.
  apply (@left_covariant_measure_radon R O mulO invO eO
    (orthogonal_group_lch hO) (fun _ => 1%R) theta); last first.
  - right; exists (fun _ : nat => [set: O]); split; first by move=> i.
    by move=> y _; exists 0%N.
  - exact: nonzero_invariant_measure_invariant htheta.1.
exact (@radon_borel_regular R O theta orthogonal_probability_is_measure hrad).
Qed.

(** Source for [orthogonal_probability_whole_countably_measurable]:
    supporting Fubini domain for 2.10.16, p. 178.
    The actual theta_n has finite total mass one, so
    no additional sigma-finiteness hypothesis is imposed. *)
Lemma orthogonal_probability_whole_countably_measurable : measure_countably_measurable theta setT.
Proof.
apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole orthogonal_probability_is_measure.
by rewrite htheta.2 ltry.
Qed.
End OrthogonalProbability.
