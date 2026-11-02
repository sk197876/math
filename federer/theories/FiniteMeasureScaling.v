(** Supporting measure scaling for the corrected associativity theorem of
    Federer (1969), 2.6.5, p. 119. We use the largest-measure
    characterisation of 2.6.1, p. 115, after division by a finite positive
    factor. Scaling follows directly from 2.1.1(6), p. 52, and 2.1.2, p. 53. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumScale MeasureUP MeasureBasic MeasureSplit ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_scale_is_measure]: supporting consequence of Federer
    2.1.1(6), p. 52, and 2.1.2, p. 53, used for the corrected associativity
    argument of 2.6.5, p. 119 (. *)
Lemma finite_scale_is_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) :
  (0 <= c)%R -> is_measure (fun A => c%:E * mu A).
Proof.
move=> hc; constructor.
- move=> A; apply: mule_ge0; last exact (measure_nonnegative hm _).
  by rewrite lee_fin.
- move=> A F hF hcover.
  rewrite nonnegative_sum_scale //; last by move=> B _; exact (measure_nonnegative hm _).
  apply: lee_wpmul2l; first by rewrite lee_fin.
  exact: measure_countable_cover hF hcover.
Qed.

(** Source for [finite_factor_product_domination]: supporting use of the
    extremal characterisation in Federer 2.6.1, p. 115, for corrected
    associativity in 2.6.5, p. 119 (. A measure whose rectangle values are
    bounded by c times the product is bounded everywhere by c times the
    Cartesian product, for finite positive c. This avoids dividing infinite
    measure values. *)
Lemma finite_factor_product_domination (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (eta : set (X * Y) -> \bar R) (he : is_measure eta) (c : R) :
  (0 < c)%R ->
  (forall A B, measure_measurable alpha A -> measure_measurable beta B ->
    eta (A `*` B) <= c%:E * (alpha A * beta B)) ->
  forall S, eta S <= c%:E * product_measure ha hb S.
Proof.
move=> hc hr S.
have hci : (0 <= c^-1)%R by rewrite invr_ge0 ltW.
have hcE : (0 <= c%:E)%E by rewrite lee_fin ltW.
have hciE : (0 <= c^-1%:E)%E by rewrite lee_fin.
have hn := finite_scale_is_measure he hci.
have hrect A B (hA : measure_measurable alpha A) (hB : measure_measurable beta B) :
    c^-1%:E * eta (A `*` B) <= alpha A * beta B.
  have h := lee_wpmul2l hciE
    (hr A B hA hB).
  rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in h.
  exact h.
have hbnd := @product_measure_greatest R X Y alpha beta ha hb
  (fun A => c^-1%:E * eta A) hn hrect S.
have h := lee_wpmul2l hcE hbnd.
rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in h.
exact h.
Qed.

(** Source for [nonnegative_finite_factor_product_domination]: zero-factor
    extension of the preceding supporting extremal bound for Federer 2.6.5,
    p. 119, corrected. When c=0, the whole rectangle forces eta to be the
    zero measure. *)
Lemma nonnegative_finite_factor_product_domination (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (eta : set (X * Y) -> \bar R) (he : is_measure eta) (c : R) :
  (0 <= c)%R ->
  (forall A B, measure_measurable alpha A -> measure_measurable beta B ->
    eta (A `*` B) <= c%:E * (alpha A * beta B)) ->
  forall S, eta S <= c%:E * product_measure ha hb S.
Proof.
move=> hc hr S; have [hc0|hcn] := eqVneq c 0%R.
- subst c; rewrite mul0e.
  have hbnd := hr setT setT (measure_measurable_whole ha) (measure_measurable_whole hb).
  rewrite mul0e in hbnd; apply: le_trans _ hbnd.
  apply: (measure_mono he)=> p _; by split.
- have hcpos : (0 < c)%R by rewrite lt_def hcn hc.
  exact (@finite_factor_product_domination R X Y alpha beta ha hb eta he c hcpos hr S).
Qed.
