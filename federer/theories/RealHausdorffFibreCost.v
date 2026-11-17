(** Federer 2.10.25, pp. 188-189: the exact product of the real-degree
    diameter costs in the first display of the proof. The original
    Gamma normalizers remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower RealPowerSuccessor RealPowerGaugeProducts
  RealHausdorffNormalisation RealHausdorffMeasure MetricRealPowerCost
  RealPowerCoverVariants RealPowerPositiveLipschitz WeakEnlargementRealPower
  LipschitzUP HausdorffLipschitzCost MetricDiameterUP MetricDiameter
  CaratheodoryNullGenerators MeasureUP MeasureBasic HausdorffLengthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_fibre_bound_constant]: the coefficient
    of the original inequality in Federer 2.10.25, p. 188. The ratio
    of the actual Gamma-normalized diameter coefficients is the printed
    alpha(k)alpha(m)/alpha(k+m), since powers of two cancel. The real
    power of the Lipschitz bound keeps 0^0=1. *)
Definition real_hausdorff_fibre_bound_constant (R : realType) (k m : R)
    (hk : (0<=k)%R) (hm : (0<=m)%R) (L : R) : R :=
  (real_power L m*(real_hausdorff_normalisation hk*real_hausdorff_normalisation hm/
    real_hausdorff_normalisation (addr_ge0 hk hm)))%R.

(** Source for [real_hausdorff_fibre_bound_constant_nonnegative]:
    supporting nonnegative coefficient in Federer 2.10.25, pp. 188-189.
    The Gamma normalization is strictly positive at every nonnegative
    real degree; zero Lipschitz bounds remain allowed. *)
Lemma real_hausdorff_fibre_bound_constant_nonnegative (R : realType) (k m : R)
    (hk : (0<=k)%R) (hm : (0<=m)%R) (L : R) :
    (0<=real_hausdorff_fibre_bound_constant hk hm L)%R.
Proof.
rewrite /real_hausdorff_fibre_bound_constant; apply: mulr_ge0;
  first exact: real_power_nonnegative.
apply: divr_ge0; last exact: ltW (real_hausdorff_normalisation_positive _).
exact: mulr_ge0 (ltW (real_hausdorff_normalisation_positive hk))
  (ltW (real_hausdorff_normalisation_positive hm)).
Qed.

(** Source for [real_hausdorff_fibre_bound_constant_positive]: supporting
    strictly positive coefficient for positive Lipschitz bound in Federer
    2.10.25, pp. 188-189. This includes both degree-zero endpoints. *)
Lemma real_hausdorff_fibre_bound_constant_positive (R : realType) (k m : R)
    (hk : (0<=k)%R) (hm : (0<=m)%R) (L : R) :
    (0<L)%R -> (0<real_hausdorff_fibre_bound_constant hk hm L)%R.
Proof.
move=> hL; rewrite /real_hausdorff_fibre_bound_constant; apply: mulr_gt0;
  first exact: real_power_strictly_positive.
apply: divr_gt0; last exact: real_hausdorff_normalisation_positive.
exact: mulr_gt0 (real_hausdorff_normalisation_positive hk)
  (real_hausdorff_normalisation_positive hm).
Qed.

(** Source for [real_hausdorff_diameter_cost_product]: supporting
    exact real-degree gauge product in the first proof display of
    Federer 2.10.25, p. 189. Zero and infinite diameters and both
    degree-zero endpoints retain the original power conventions. *)
Lemma real_hausdorff_diameter_cost_product (R : realType) (X : metricType R)
    (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) (S : set X) :
    metric_real_diameter_cost (real_hausdorff_normalisation hk) k S*
      metric_real_diameter_cost (real_hausdorff_normalisation hm) m S=
    (real_hausdorff_normalisation hk*real_hausdorff_normalisation hm/
      real_hausdorff_normalisation (addr_ge0 hk hm))%R%:E*
      metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk hm)) (k+m)%R S.
Proof.
have hn : real_hausdorff_normalisation (addr_ge0 hk hm)!=0%R :=
  lt0r_neq0 (real_hausdorff_normalisation_positive _).
rewrite /metric_real_diameter_cost /metric_real_power_cost muleACA -EFinM.
rewrite -extended_metric_real_power_add_nonnegative //;
  last exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
by rewrite muleA -EFinM divfK.
Qed.

(** Source for [real_hausdorff_closed_image_fibre_cost_bound]: the
    first proof display of Federer 2.10.25, p. 189, in every
    nonnegative real degree. Reuse Lipschitz diameter control, closure
    invariance and the exact real-power scaling law. The positive-bound
    case supplies the weighted-cover proof; its zero-bound case is
    handled by the existing null-image method in the final theorem. *)
Theorem real_hausdorff_closed_image_fibre_cost_bound (R : realType)
    (X Y : metricType R) (f : X -> Y) (L k m : R)
    (hk : (0<=k)%R) (hm : (0<=m)%R) :
    is_metric_lipschitz_bound setT f L -> (0<L)%R -> forall S,
    metric_real_diameter_cost (real_hausdorff_normalisation hk) k S*
      metric_real_diameter_cost (real_hausdorff_normalisation hm) m (closure (f @` S))<=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E*
      metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk hm)) (k+m)%R S.
Proof.
move=> hf hL S; rewrite metric_real_diameter_cost_closure.
have hdiam := @extended_metric_diameter_lipschitz R X Y f L hf S.
have hcost := @metric_real_power_cost_monotone R (real_hausdorff_normalisation hm) m
  (extended_metric_diameter (f @` S)) (L%:E*extended_metric_diameter S)
  (ltW (real_hausdorff_normalisation_positive hm)) hm
  (metric_diameter_nonnegative (extended_metric_diameter_specification (f @` S))) hdiam.
rewrite (@metric_real_power_cost_positive_scale R (real_hausdorff_normalisation hm) m
  L (extended_metric_diameter S) hL
  (metric_diameter_nonnegative (extended_metric_diameter_specification S))) in hcost.
have hkn := @metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hk) k S
  (ltW (real_hausdorff_normalisation_positive hk)).
have hcostD : metric_real_diameter_cost (real_hausdorff_normalisation hm) m (f @` S)<=
    (real_power L m)%:E*metric_real_diameter_cost (real_hausdorff_normalisation hm) m S := hcost.
have hh := lee_wpmul2l hkn hcostD.
have he : metric_real_diameter_cost (real_hausdorff_normalisation hk) k S*
    ((real_power L m)%:E*metric_real_diameter_cost (real_hausdorff_normalisation hm) m S)=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E*
      metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk hm)) (k+m)%R S.
  by rewrite muleCA (real_hausdorff_diameter_cost_product hk hm S) muleA -EFinM.
by rewrite he in hh.
Qed.

(** Source for [real_hausdorff_zero_cost_generator_null]: supporting
    removal of infinite grouped weights in Federer 2.10.25, p. 189.
    A zero real-degree cost forces zero diameter, so the original
    singleton-cover bound holds at every positive cutoff. The empty
    target is treated by its measure law; no empty generator is used. *)
Theorem real_hausdorff_zero_cost_generator_null (R : realType) (X : metricType R)
    (p : R) (hp : (0<=p)%R) (S : set X) :
    metric_real_diameter_cost (real_hausdorff_normalisation hp) p S=0 ->
      @real_hausdorff_measure R X p hp S=0.
Proof.
move=> hz.
have hm := @real_hausdorff_measure_is_measure R X p hp.
have hn := real_hausdorff_normalisation_positive hp.
have hzero : extended_metric_diameter S=0.
  apply/eqP; rewrite eq_le
    (metric_diameter_nonnegative (extended_metric_diameter_specification S)) andbT leNgt.
  apply/negP => hd.
  have hpow : 0<extended_metric_real_power (extended_metric_diameter S) p.
    move: hd; case he: (extended_metric_diameter S) => [d| |] hd; last by [].
    - rewrite extended_metric_real_power_finite lte_fin.
      apply: real_power_strictly_positive; by move: hd; rewrite lte_fin.
    - rewrite /extended_metric_real_power; case: ifP => _; by [].
  have hcpos : 0<metric_real_diameter_cost (real_hausdorff_normalisation hp) p S.
    apply: mule_gt0 => //; by rewrite lte_fin.
  by rewrite hz ltxx in hcpos.
case: (pselect (S!=set0)) => [hS|hempty].
- pose j : @nonempty_metric_sets R X := Sub S (mem_set hS).
  have hcost := @metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hp) p S (ltW hn).
  have hh := @caratheodory_zero_diameter_generator_bound R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j))
    (@real_hausdorff_measure R X p hp) j (@real_hausdorff_measure_specification R X p hp) hcost hzero.
  rewrite hz in hh; apply/eqP; rewrite eq_le hh /=; exact: (@measure_nonnegative R X (@real_hausdorff_measure R X p hp) hm S).
- have he : S=set0.
    apply/seteqP; split=> [x hx|x []]; exfalso; apply: hempty; by exists x.
  rewrite he; exact: measure_empty hm.
Qed.
