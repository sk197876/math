(** Federer (1969), 2.10.25, pp. 188–189: supporting cost product in the
    first display of the proof, with coefficient Lip(f)^m alpha(k)
    alpha(m)/alpha(k+m). Prove the normalization cancellation and
    diameter-power identity, then use the Lipschitz image bound and closure
    invariance. These are integer-degree statements, including zero degrees
    and zero Lipschitz bounds; optional real-degree Gamma extensions are not
    assumed. Neither is cited as the identical fibre theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanBallVolume LipschitzUP MetricDiameterUP MetricDiameter
  HausdorffDiameterCost HausdorffLipschitzCost HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  CaratheodoryNullGenerators MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_natural_power_add]: supporting integer
    power identity for the first cost display in
    2.10.25, p. 189. Includes zero and infinite
    diameters with the established zeroth-power convention. *)
Lemma extended_natural_power_add (R : realType) (d : \bar R) (k m : nat) :
  d^+(k+m)=d^+k*d^+m.
Proof.
elim: k=> [|k ih]; first by rewrite add0n expe0 mul1e.
by rewrite addSn !expeS ih muleA.
Qed.

(** Source for [hausdorff_fibre_bound_constant]: direct coefficient
    of the estimate in 2.10.25, p. 188, and the
    first line of its proof on p. 189. The scalar
    L is any proved nonnegative Lipschitz bound. *)
Definition hausdorff_fibre_bound_constant (R : realType) (k m : nat) (L : R) : R :=
  (L^+m*(euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/
    euclidean_unit_ball_volume R (k+m)))%R.

(** Source for [hausdorff_fibre_bound_constant_nonnegative]: supporting
    nonnegativity of the displayed coefficient in 2.10.25,
    pp. 188–189, from the positive unit-ball volumes
    of 2.7.16(1), p. 135. Zero bounds and degree
    zero retain the existing power conventions. *)
Lemma hausdorff_fibre_bound_constant_nonnegative (R : realType) (k m : nat) (L : R) :
  (0<=L)%R -> (0<=hausdorff_fibre_bound_constant k m L)%R.
Proof.
move=> hL; rewrite /hausdorff_fibre_bound_constant; apply: mulr_ge0; first exact: exprn_ge0 hL.
apply: divr_ge0; last exact: ltW (euclidean_unit_ball_volumeE R (k+m)).2.
exact: mulr_ge0 (ltW (euclidean_unit_ball_volumeE R k).2) (ltW (euclidean_unit_ball_volumeE R m).2).
Qed.

(** Source for [hausdorff_normalisation_product]: supporting
    cancellation of the powers of two in the
    first display of the proof of 2.10.25, p. 189,
    using the printed normalization in 2.10.2, p. 171.
    No computation through the unit-ball measure is used. *)
Lemma hausdorff_normalisation_product (R : realType) (k m : nat) :
  ((euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/euclidean_unit_ball_volume R (k+m))*
    hausdorff_normalisation R (k+m))%R=
    (hausdorff_normalisation R k*hausdorff_normalisation R m)%R.
Proof.
have ha : (euclidean_unit_ball_volume R (k+m)!=0)%R.
  by rewrite gt_eqF //; exact: (euclidean_unit_ball_volumeE R (k+m)).2.
by rewrite /hausdorff_normalisation !mulf_div exprD invfM !mulrA mulfK.
Qed.

(** Source for [hausdorff_diameter_cost_product]: supporting
    exact same-set gauge product for the first display
    in the proof of 2.10.25, p. 189. This identity
    permits unbounded and empty sets as numerical notation;
    actual Hausdorff generators remain nonempty. *)
Lemma hausdorff_diameter_cost_product (R : realType) (X : metricType R) (k m : nat) (S : set X) :
  hausdorff_diameter_cost k S*hausdorff_diameter_cost m S=
    (euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/euclidean_unit_ball_volume R (k+m))%R%:E*
    hausdorff_diameter_cost (k+m) S.
Proof.
rewrite /hausdorff_diameter_cost /hausdorff_power_cost.
rewrite muleACA -EFinM -extended_natural_power_add.
by rewrite -(@hausdorff_normalisation_product R k m) EFinM -muleA.
Qed.

(** Source for [hausdorff_closed_image_fibre_cost_bound]: direct
    integer-degree product inequality in the first display
    of the proof of 2.10.25, p. 189. Closures of
    image generators preserve diameter. Arbitrary proved
    Lipschitz bounds, including zero, are allowed. *)
Theorem hausdorff_closed_image_fibre_cost_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) (k m : nat) : is_metric_lipschitz_bound setT f L ->
  forall S, hausdorff_diameter_cost k S*hausdorff_diameter_cost m (closure (f @` S))<=
    (hausdorff_fibre_bound_constant k m L)%:E*hausdorff_diameter_cost (k+m) S.
Proof.
move=> hf S; rewrite hausdorff_diameter_cost_closure.
have hh := lee_wpmul2l (hausdorff_diameter_cost_nonnegative k S)
  (@hausdorff_lipschitz_cost_bound R X Y f L m hf S).
have he : hausdorff_diameter_cost k S*((L^+m)%R%:E*hausdorff_diameter_cost m S)=
    (hausdorff_fibre_bound_constant k m L)%:E*hausdorff_diameter_cost (k+m) S.
  by rewrite muleCA hausdorff_diameter_cost_product muleA -EFinM.
by rewrite he in hh.
Qed.

(** Source for [hausdorff_zero_cost_generator_null]: supporting
    removal of infinite grouped weights in the proof
    of 2.10.25, p. 189. A zero Hausdorff generator
    cost forces zero diameter in positive degree and
    hence zero final mass. Degree zero has cost one,
    so no zero-cost generator is silently introduced. *)
Theorem hausdorff_zero_cost_generator_null (R : realType) (X : metricType R) (m : nat) (S : set X) :
  hausdorff_diameter_cost m S=0 -> @hausdorff_measure R X m S=0.
Proof.
move=> hz.
have hm := @hausdorff_measure_is_measure R X m.
have hn := @hausdorff_normalisation_positive R m.
have hzero : extended_metric_diameter S=0.
  have hh : hausdorff_diameter_cost m S==0 by apply/eqP.
  move: hh; rewrite /hausdorff_diameter_cost /hausdorff_power_cost mule_eq0 eqe (gt_eqF hn) /= expe_eq0.
  by move=> /andP[_ /eqP].
case: (pselect (S !=set0))=> [hS|hS].
- pose j : @nonempty_metric_sets R X := Sub S (mem_set hS).
  have hh := @caratheodory_zero_diameter_generator_bound R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) (@hausdorff_measure R X m) j
    (@hausdorff_measure_specification R X m) (hausdorff_diameter_cost_nonnegative m S) hzero.
  change (is_true (hausdorff_measure m S<=hausdorff_diameter_cost m S)) in hh.
  rewrite hz in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative hm S).
- have he : S=set0 by apply/seteqP; split=> [x hx|x []]; exfalso; apply: hS; by exists x.
  rewrite he; exact: measure_empty hm.
Qed.
