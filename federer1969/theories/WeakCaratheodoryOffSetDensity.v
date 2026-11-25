(** Supporting weak-cost density consequence for Federer (1969),
    2.10.19(3)–(5), p. 181. The corrected covering quotient permits zero
    costs; original metric-density normalisations stay positive. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction BorelRegularMeasureUP
  BorelRegularApproximation ClosedApproximationUP CaratheodoryLimitUP CaratheodoryLimitMeasure
  CaratheodoryWeakEnlargementUP WeakCaratheodoryEnlargementDensityBound CaratheodoryDensityUpperBound
  MeasureDerivates CoveringRelationLimits ExtendedScaledErrorBound.
From Federer Require Import WeakCaratheodoryDensityQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_off_set_density_level_null]: supporting
    weak-cost density estimate for 2.10.19(3)–(5), p. 181 This explicitly
    uses the corrected covering quotient and controlled containing
    generators. *)
Theorem weak_caratheodory_off_set_density_level_null (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : set X) (t : R) :
  is_weak_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  measure_measurable mu A -> mu A < +oo -> (0<t)%R ->
  psi [set x | ~ A x /\ t%:E<covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio (measure_restrict mu A) c) x]=0.
Proof.
move=> hE hm hr hpsi hclosed hmeas hA hAf ht.
pose B := [set x | ~ A x /\ t%:E<covering_upper_limit (caratheodory_family_relation F)
  (caratheodory_measure_cost_ratio (measure_restrict mu A) c) x].
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: (@weak_enlargement_cost_nonnegative R X F c E k hE _ (set_valP j)).
have hpm := caratheodory_limit_is_measure hpsi hcost.
have hz : t%:E*psi B<=(0%R : R)%:E.
  apply: (@extended_upper_bound_from_scaled_errors R (t%:E*psi B) 0%R 1%R (@ler01 R))=> e he.
  have [C [hC [hCA herr]]] := @borel_regular_closed_approximation R X mu hm hr A hA hAf e he.
  have hV : B `<=` ~` C by move=> x [hn _] hc; apply: hn; exact: hCA.
  have hmeasA S (hS : F S) : measure_measurable (measure_restrict mu A) S.
    exact: measure_restrict_measurable (hmeas S hS).
  have hh := @weak_caratheodory_enlargement_density_bound R X F c (measure_restrict mu A) psi E k
    B (~` C) t hE (measure_restrict_is_measure hm A) hpsi hclosed hmeasA
    (closed_openC hC) hV ht (fun x hx => hx.2).
  have hfinal : t%:E*psi B<=e%:E := le_trans hh (ltW herr).
  by rewrite mul1r add0r.
have hti : 0<=(t^-1)%R%:E by rewrite lee_fin invr_ge0; exact: ltW ht.
have hh := lee_wpmul2l hti hz.
rewrite muleA -EFinM mulVf ?gt_eqF // mul1e mule0 in hh.
apply/eqP; by rewrite eq_le (@measure_nonnegative R X psi hpm B) andbT.
Qed.
