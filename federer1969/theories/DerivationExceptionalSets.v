(** The exceptional sets Q and R(a,b) in Federer (1969), 2.9.5, pp. 154–155.
    Use the two comparisons of 2.9.4 on bounded subsets and then a countable
    bounded exhaustion. Here the original M makes both measures finite on
    every bounded piece, as in Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates
  CoveringRelationLimits CoveringFamilyUP MeasureUP MeasureBasic AbsoluteContinuousPart
  DerivationComparison DerivationExceptionalArithmetic BoundedNullLocalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_infinite_upper_points]: the set Q
    in the proof of Federer 2.9.5, p. 154:
    points with positive-infinite upper V ratio limit. *)
Definition derivation_infinite_upper_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) :=
  [set x | covering_upper_limit V (measure_ratio_function psi phi) x=+oo].

(** Source for [derivation_gap_points]: the sets R(a,b)
    in Federer 2.9.5, p. 154, written with
    two strict inequalities. The positive rational indexing
    used later is sufficient once lower limits are nonnegative. *)
Definition derivation_gap_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) (a b : R) :=
  [set x | covering_lower_limit V (measure_ratio_function psi phi) x<a%:E /\
    b%:E<covering_upper_limit V (measure_ratio_function psi phi) x].

(** Source for [derivation_infinite_upper_points_null]: nullity
    of Q in Federer 2.9.5, p. 155.
    For a bounded target, 2.9.4 bounds every positive
    multiple of phi(A) by the finite value psi(A).
    Countable bounded localisation gives the global assertion. *)
Lemma derivation_infinite_upper_points_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  phi (derivation_infinite_upper_points psi phi V)=0.
Proof.
move=> hc hp; have hf := derivation_context_measure hc.
have hmf := derivation_measure_law hf.
have hmp := derivation_measure_law hp.
apply: (@measure_null_of_bounded_subsets R X phi _ hmf)=> A hbounded hA.
apply (@finite_all_scaled_bounds_zero R (phi A) (psi A)
  (measure_nonnegative hmf A) (@derivation_measure_bounded_finite R X phi hf A hbounded)
  (measure_nonnegative hmp A) (@derivation_measure_bounded_finite R X psi hp A hbounded)).
move=> c hcpos.
have hlow := @derivation_upper_comparison R X phi psi V A c hc hp hcpos.
have hupper := @measure_continuous_part_le R X psi phi hmf (derivation_measure_borel_regular hp) A.
apply: le_trans _ hupper; apply: hlow=> x hx.
rewrite (hA x hx); exact: ltry.
Qed.

(** Source for [derivation_gap_points_null]: nullity of R(a,b) for 0<a<b in
    Federer 2.9.5, p. 155 The finite bounded-set comparison has no
    measurability premise on the target. *)
Lemma derivation_gap_points_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) (a b : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<a)%R -> (a<b)%R ->
  phi (derivation_gap_points psi phi V a b)=0.
Proof.
move=> hc hp ha hab; have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
have hb : (0<b)%R := lt_trans ha hab.
apply: (@measure_null_of_bounded_subsets R X phi _ hm)=> A hbounded hA.
have hlow : b%:E*phi A<=measure_continuous_part psi phi A.
  apply: (@derivation_upper_comparison R X phi psi V A b hc hp hb)=> x hx.
  exact: (hA x hx).2.
have hupper : measure_continuous_part psi phi A<=a%:E*phi A.
  apply: (@derivation_lower_comparison R X phi psi V A a hc hp ha)=> x hx.
  exact: (hA x hx).1.
exact (@finite_separated_scaled_bounds_zero R (phi A) (measure_continuous_part psi phi A)
  a b (measure_nonnegative hm A) (@derivation_measure_bounded_finite R X phi hf A hbounded) hab hlow hupper).
Qed.
