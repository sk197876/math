(** Federer (1969), 2.9.4, p. 154, both strict lower- and upper-limit
    comparisons. The lower estimate applies 2.9.3 with denominator phi; the
    upper estimate reverses the quotient and uses threshold 1/c. the
    numbered theorem below retains Federer's strict ones and the original M. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates CoveringRelationLimits
  MeasureUP AbsoluteContinuousPart MeasureAbsoluteContinuity
  DerivationLowerComparison DerivationReciprocalLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_continuous_part_self]: the opening
    identity phi_phi=phi in the proof of Federer 2.9.4,
    p. 154. It follows from the equality
    criterion 2.9.2, p. 153, since phi is
    absolutely continuous with respect to itself. No finite
    total mass is needed. *)
Lemma measure_continuous_part_self (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi -> measure_continuous_part phi phi=phi.
Proof.
move=> hphi; symmetry.
apply: (@continuous_part_equality_iff_absolute_continuity R X phi phi
  (measure_continuous_part phi phi) (derivation_measure_law hphi)
  (derivation_measure_law hphi) (derivation_measure_borel_regular hphi)
  (measure_continuous_part_specification phi phi)).2.
by move=> A hz.
Qed.

(** Source for [derivation_lower_comparison]: first implication
    of Federer 2.9.4, p. 154: a strict
    lower ratio-limit bound on A gives psi_phi(A)<=c phi(A).
    This is 2.9.3 and phi_phi=phi. *)
Lemma derivation_lower_comparison (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A (c : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<c)%R ->
  (forall x, A x -> covering_lower_limit V (measure_ratio_function psi phi) x<c%:E) ->
  measure_continuous_part psi phi A<=c%:E*phi A.
Proof.
move=> hc hpsi hp hA.
have hphi := derivation_context_measure hc.
have h := @federer_2_9_3 R X phi psi phi V A c hc hpsi hphi hp hA.
by rewrite (measure_continuous_part_self hphi) in h.
Qed.

(** Source for [derivation_upper_comparison]: second implication
    of Federer 2.9.4, p. 154: a strict
    upper ratio-limit lower bound on A gives c phi(A)<=psi_phi(A).
    Reverse the partial quotient on bounded cells, then apply
    2.9.3 with positive finite threshold 1/c. *)
Lemma derivation_upper_comparison (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) A (c : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<c)%R ->
  (forall x, A x -> c%:E<covering_upper_limit V (measure_ratio_function psi phi) x) ->
  c%:E*phi A<=measure_continuous_part psi phi A.
Proof.
move=> hc hpsi hp hA.
have hphi := derivation_context_measure hc.
have hinv : (0<c^-1)%R by rewrite invr_gt0.
have hrev x : A x -> covering_lower_limit V (measure_ratio_function phi psi) x<(c^-1)%:E.
  move=> hx; exact (@derivation_strict_reciprocal_limit R X psi phi V x c hpsi hphi hp (hA x hx)).
have h := @federer_2_9_3 R X phi phi psi V A (c^-1)%R hc hphi hpsi hinv hrev.
rewrite (measure_continuous_part_self hphi) in h.
have hpE : 0<=c%:E by rewrite lee_fin; exact: ltW hp.
have hmul := @lee_wpmul2l R c%:E hpE _ _ h.
by rewrite muleA -EFinM mulfV ?gt_eqF ?mul1e in hmul.
Qed.

(** Source for [federer_2_9_4]: direct complete corollary
    Federer 2.9.4, p. 154, retaining both
    strict set-inclusion premises. Every target is arbitrary;
    nonmeasurable targets and infinite measure values are
    included, with no extra total-mass assumption. *)
Theorem federer_2_9_4 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) (c : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi -> (0<c)%R ->
  (forall A, (forall x, A x -> covering_lower_limit V (measure_ratio_function psi phi) x<c%:E) ->
    measure_continuous_part psi phi A<=c%:E*phi A) /\
  (forall A, (forall x, A x -> c%:E<covering_upper_limit V (measure_ratio_function psi phi) x) ->
    c%:E*phi A<=measure_continuous_part psi phi A).
Proof.
move=> hc hpsi hp; split=> A hA.
- exact (@derivation_lower_comparison R X phi psi V A c hc hpsi hp hA).
- exact (@derivation_upper_comparison R X phi psi V A c hc hpsi hp hA).
Qed.
