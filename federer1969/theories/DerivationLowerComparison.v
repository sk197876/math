(** Federer (1969), 2.9.3, p. 154, including the strict lower-limit
    hypothesis exactly as printed. its proof supplies open approximation and
    the Vitali selection. The theorem below retains the original class M and
    strict premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates CoveringRelationLimits
  MeasureUP MeasureBasic AbsoluteContinuousPart AbsoluteContinuousPartBasic
  ContinuousPartOpenApproximation DerivationSublevelSelection ScaledMeasureApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_9_3]: direct formalisation of
    Federer 2.9.3, p. 154: for alpha,beta in M,
    0<c<infinity and lower V limit of alpha/beta strictly
    below c on A, alpha_phi(A)<=c beta_phi(A).
    Undefined quotient values remain outside the partial graph.
    The target A may be arbitrary and the measures infinite. *)
Theorem federer_2_9_3 (R : realType) (X : metricType R)
    (phi alpha beta : set X -> \bar R) (V : X -> set X -> Prop)
    (A : set X) (c : R) :
  is_measure_derivation_context phi V ->
  is_derivation_measure alpha -> is_derivation_measure beta -> (0<c)%R ->
  (forall x, A x -> covering_lower_limit V (measure_ratio_function alpha beta) x<c%:E) ->
  measure_continuous_part alpha phi A<=c%:E*measure_continuous_part beta phi A.
Proof.
move=> hc ha hb hcpos hA.
have hmphi := derivation_measure_law (derivation_context_measure hc).
apply: (@scaled_nonnegative_measure_approximation_bound R
  (measure_continuous_part alpha phi A) (measure_continuous_part beta phi A) c).
- exact (@continuous_part_nonnegative R X phi beta (measure_continuous_part beta phi)
    (derivation_measure_law hb) (measure_continuous_part_specification beta phi) A).
- exact hcpos.
- move=> e he.
  have [W [hW [hz hbeta]]] := @continuous_part_open_almost_cover R X phi beta A e hmphi hb he.
  have h := @derivation_lower_sublevel_open_bound R X phi alpha beta V A W c hc ha hb hcpos hW hz hA.
  apply: le_trans h _; apply: lee_wpmul2l; last exact hbeta.
  by rewrite lee_fin; exact: ltW hcpos.
Qed.
