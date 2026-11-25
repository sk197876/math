(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureDerivationContext MeasureRestriction
  NullBallLocus CenteredRatioInfinity CenteredRatioBorel CenteredDensityGeometry
  CenteredDensityNullComparison ContinuousPartExceptionalRestriction AbsoluteContinuousPart
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_9_15]: complete theorem of Federer
    2.9.15, pp. 160–161. Retain both original geometric
    alternatives, psi in M, and the standing phi Vitali
    context of 2.9.1, p. 152. W is the infinite radius-
    density locus, P is the open null-ball locus, and the
    continuous part is precisely psi restricted to the
    complement of W union P. The proof follows the two
    printed covering cases, with the citation corrected to
    2.8.14 by erratum p. 3, book p. 161 line 11. *)
Theorem federer_2_9_15 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V0 : X -> set X -> Prop) :
  is_measure_derivation_context phi V0 -> is_derivation_measure psi ->
  is_centered_density_geometry phi ->
  borel_set (measure_infinite_centered_density_points psi phi) /\
  open (measure_null_ball_points phi) /\
  measure_continuous_part psi phi=measure_restrict psi
    (~` (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi)).
Proof.
move=> hc hpsi hgeo; have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hp := derivation_measure_law hpsi.
split; first exact: measure_infinite_centered_density_points_borel hphi hpsi.
split; first exact: measure_null_ball_points_open hm.
apply: (@continuous_part_exceptional_restriction R X phi psi (measure_continuous_part psi phi)
  (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi)
  hm hp (@measure_continuous_part_is_measure R X psi phi hm hp)
  (derivation_measure_borel_regular hpsi) (measure_continuous_part_specification psi phi)
  (@centered_density_exceptional_union_null R X phi psi V0 hc hpsi hgeo)).
move=> T hT hz; exact: geometric_null_set_outside_infinite_density hphi hp hgeo hT hz.
Qed.
