(** Federer (1969), 2.10.20, p. 182: the corresponding exhaustion for the
    final measure follows because closed balls are measurable. Apply
    increasing measurable-set continuity to the restriction by A, so A
    itself need not be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureFiniteClosure MeasureContinuityBelow
  MetricClosedBalls ExtendedRealOrderLimit ExtendedRealLimitBounds RadialMassSupremum
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryMetricMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_ball_radial_mass_supremum]: supporting
    closed-ball measurability argument for the final
    measure in 2.10.20, p. 182. Apply 2.1.3(4),
    p. 55, to mu restricted to arbitrary A and
    the measurable balls of natural radius. *)
Lemma measurable_ball_radial_mass_supremum (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (A : set X) :
  is_measure mu -> (forall r : R, measure_measurable mu (metric_closed_ball a r)) ->
  mu A=radial_mass_supremum mu a A.
Proof.
move=> hm hBall.
have hn := measure_restrict_is_measure hm A.
have hBn n : measure_measurable (measure_restrict mu A) (metric_closed_ball a n%:R).
  exact: (@measure_restrict_measurable R X mu A _ (hBall n%:R)).
have hmono n m (hnm : (n<=m)%N) : metric_closed_ball a n%:R `<=` metric_closed_ball a m%:R.
  move=> x hx; have hcast : (n%:R<=m%:R :> R)%R by rewrite ler_nat.
  exact: le_trans hx hcast.
have hcover : (\bigcup_n metric_closed_ball a n%:R)=@setT X.
  apply/seteqP; split=> [x hx//|x _].
  pose n := Num.bound (mdist a x).
  have hbound : (mdist a x<n%:R)%R by apply: archi_boundP; exact: mdist_ge0.
  exists n=> //; exact: ltW hbound.
have hlim := @measure_continuity_below R X (measure_restrict mu A) hn
  (fun n => metric_closed_ball a n%:R) hBn hmono.
rewrite hcover /measure_restrict setIT in hlim.
have hbound n : mu (A `&` metric_closed_ball a n%:R)<=radial_mass_supremum mu a A.
  exact: radial_mass_le_supremum.
have hle := extended_order_limit_upper_bound hlim.2 hbound.
apply/eqP; rewrite eq_le (radial_mass_supremum_le_total a A hm) andbT; exact hle.
Qed.

(** Source for [measurable_ball_radial_continuity]: supporting
    radial limit for the final measure in 2.10.20,
    p. 182. The conclusion holds for any measure
    with measurable closed balls, including arbitrary A
    and infinite total mass. *)
Theorem measurable_ball_radial_continuity (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (A : set X) :
  is_measure mu -> (forall r : R, measure_measurable mu (metric_closed_ball a r)) ->
  unbounded_radius_order_limit (fun r => mu (A `&` metric_closed_ball a r)) (mu A).
Proof.
move=> hm hBall.
have he := @measurable_ball_radial_mass_supremum R X mu a A hm hBall.
have hlim := radial_mass_has_supremum_limit a A hm.
by rewrite -he in hlim.
Qed.

(** Source for [federer_2_10_20_final_measure_radial]: the
    corresponding final-measure proposition in 2.10.20,
    p. 182: "because closed balls are psi measurable".
    Their measurability is proved from the Caratheodory
    laws; no Borel generators or Borel regularity is assumed. *)
Theorem federer_2_10_20_final_measure_radial (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (psi : set X -> \bar R) (A : set X) (a : X) :
  (forall S, F S -> 0<=c S) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  unbounded_radius_order_limit (fun r => psi (A `&` metric_closed_ball a r)) (psi A).
Proof.
move=> hc hpsi.
have hcost (j : set_type F) : 0<=c (val j) := hc _ (set_valP j).
have hm := caratheodory_limit_is_measure hpsi hcost.
apply: (@measurable_ball_radial_continuity R X psi a A hm)=> r.
have hopen := closed_openC (@metric_closed_ball_closed R X a r).
have hcomp := @caratheodory_limit_open_measurable R X [the choiceType of set_type F]
  (fun j => val j) (fun j => c (val j)) psi hpsi hcost (~` metric_closed_ball a r) hopen.
have hmeas := measure_measurable_complement hcomp.
by rewrite setCK in hmeas.
Qed.
