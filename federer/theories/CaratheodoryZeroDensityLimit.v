(** Federer (1969), 2.10.18(2), p. 180: the full covering limit of mu
    restricted to A divided by zeta is zero outside A, almost everywhere for
    psi. Here the original partial quotient and Federer's finite measurable
    A hypotheses are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryEnlargementUP
  CaratheodoryEnlargementGrowth DiameterEnlargements CaratheodoryOffSetDensity CaratheodoryPositiveCostLimits
  CaratheodoryDensityUpperBound MeasureDerivates PartialFunctionUP CoveringRelationUP CoveringRelationLimits
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_extended_reciprocal_below]: supporting
    exhaustion by the positive levels 1/n in
    2.10.18(2), p. 180. Positive infinity is
    included; this is an Archimedean auxiliary fact. *)
Lemma positive_extended_reciprocal_below (R : realType) (z : \bar R) :
  0<z -> exists n : nat, (((n.+1)%:R : R)^-1)%:E<z.
Proof.
case: z=> [r| |] hp //.
- rewrite lte_fin in hp; have [n hn] := positive_reciprocal_nat_small hp.
  exists n; by rewrite lte_fin.
- exists 0%N; exact: ltry.
Qed.

(** Source for [caratheodory_off_set_zero_density]: direct
    conclusion of 2.10.18(2), p. 180, with a
    controlled containing enlargement. Both upper and lower
    limits equal zero, and the actual quotient domain is
    fine; this proves a full limit, not only a limsup. *)
Theorem caratheodory_off_set_zero_density (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : set X) :
  is_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  measure_measurable mu A -> mu A < +oo ->
  measure_almost_everywhere_on psi (~` A)
    [set x | partial_function_graph (measure_derivate (measure_restrict mu A) c
      (caratheodory_family_relation F)) x 0].
Proof.
move=> hE hm hr hf hpsi hclosed hmeas hA hAf.
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE _ (set_valP j)).
have hpm := caratheodory_limit_is_measure hpsi hcost.
pose L x := covering_upper_limit (caratheodory_family_relation F)
  (measure_ratio_function (measure_restrict mu A) c) x.
pose B n := [set x | ~ A x /\ (((n.+1)%:R : R)^-1)%:E<L x].
have hB n : psi (B n)=0.
  apply: (@caratheodory_off_set_density_level_null R X F c mu psi E k A _ hE hm hr
    hpsi hclosed hmeas hA hAf).
  by rewrite invr_gt0 ltr0n.
have hN : psi (\bigcup_n B n)=0.
  exact: (@measure_null_countable_union R X [the choiceType of (nat : Type)] psi hpm
    setT B (countableP _) (fun n _ => hB n)).
apply: (@measure_null_subset R X psi hpm _ (\bigcup_n B n))=> // x [hnA hnot].
case: (pselect (0<L x))=> hp.
- have [n hn] := positive_extended_reciprocal_below hp.
  exists n=> //; by split.
- exfalso; apply: hnot.
  have [hl horder] := @caratheodory_positive_cost_limits R X F c (measure_restrict mu A) E k x
    hE (measure_restrict_is_measure hm A) (hf x).
  have hu : L x<=0 by rewrite leNgt; apply/negP.
  have h0 : L x=0 by apply/eqP; rewrite eq_le hu /=; exact: le_trans hl horder.
  have hl0 : covering_lower_limit (caratheodory_family_relation F)
      (measure_ratio_function (measure_restrict mu A) c) x=0.
    apply/eqP; rewrite eq_le hl andbT; exact: le_trans horder hu.
  by rewrite /measure_derivate /covering_relation_limit /=; split=> //; split.
Qed.

(** Source for [federer_2_10_18_2]: direct formalisation
    of 2.10.18(2), p. 180. A is measurable
    with finite mu measure; the conclusion is the
    original partial quotient's full limit zero outside A. *)
Theorem federer_2_10_18_2 (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R) (eta : R) (A : set X) :
  is_measure mu -> is_borel_regular_measure mu -> (forall S, F S -> 0<=c S) ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (forall S, F S -> F (diameter_enlargement F S)) ->
  (forall S, F S -> c (diameter_enlargement F S)<eta%:E*c S /\ eta%:E*c S < +oo) ->
  measure_measurable mu A -> mu A < +oo ->
  measure_almost_everywhere_on psi (~` A)
    [set x | partial_function_graph (measure_derivate (measure_restrict mu A) c
      (caratheodory_family_relation F)) x 0].
Proof.
move=> hm hr hc hf hpsi hclosed hmeas hF hg hA hAf.
have hE := federer_caratheodory_enlargement_laws hc hF hg.
exact: caratheodory_off_set_zero_density hE hm hr hf hpsi hclosed hmeas hA hAf.
Qed.
