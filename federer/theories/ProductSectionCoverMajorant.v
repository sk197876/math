(** Federer (1969), 2.6.2, p. 116: compare the characteristic function of a
    covered set with the sum of the covering rectangle characteristics.
    Integrating first in one factor gives the nonnegative section majorant
    used here. No section measurability is assumed for the covered set; only
    the rectangle factors are required to be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureIndexedCover CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureExtendedCharacteristicIntegral TotalNonnegativeSeriesIntegral
  NonnegativeSum NonnegativeSumSupport ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_section_cover_integral_majorant]: supporting
    one-coordinate integration of the rectangle-cover comparison in Federer
    2.6.2, p. 116 The section measure, whether or not measurable as a
    function of x, is bounded by a measurable nonnegative function with
    integral equal to the cover cost. *)
Lemma product_section_cover_integral_majorant (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (S : set (X * Y)) (C : nat -> set X) (D : nat -> set Y) :
  (forall n, measure_measurable alpha (C n) /\ measure_measurable beta (D n)) ->
  S `<=` (\bigcup_n (C n `*` D n)) ->
  exists u : X -> extended_real_line R,
    (forall x, 0 <= u x) /\
    is_measure_integral alpha (partial_function_total u)
      (nonnegative_sum setT (fun n => alpha (C n)*beta (D n))) /\
    (forall x, beta (product_vertical_section S x) <= u x).
Proof.
move=> hm hc.
pose t n := @CharacteristicFunction.value R X (C n).
have ht n : is_characteristic_function (C n) (t n) := CharacteristicFunction.laws R (C n).
pose f n x : extended_real_line R := beta (D n)*(t n x)%:E.
have hp n x : 0 <= f n x.
  exact: mule_ge0 (measure_nonnegative hb _) (characteristic_extended_nonnegative (ht n) x).
have hi n : is_measure_integral alpha (partial_function_total (f n)) (beta (D n)*alpha (C n)).
  exact (@measure_nonnegative_extended_characteristic_integral R X alpha ha (C n) (t n)
    (beta (D n)) (ht n) (hm n).1 (measure_nonnegative hb _)).
pose u x : extended_real_line R := nonnegative_sum setT (fun n => f n x).
exists u; split; first by move=> x; exact: nonnegative_sum_nonnegative.
split.
- have hsum := @total_nonnegative_series_integral R X alpha ha f _ hp hi.
  have he : nonnegative_sum setT (fun n => beta (D n)*alpha (C n)) =
      nonnegative_sum setT (fun n => alpha (C n)*beta (D n)).
    apply: nonnegative_sum_ext=> n _; exact: muleC.
  by rewrite he in hsum.
- move=> x; pose F n : set Y := if pselect (C n x) then D n else set0.
  have hcov : product_vertical_section S x `<=` \bigcup_n F n.
    move=> y hy; have [n _ [hcx hdy]] := hc (x,y) hy.
    exists n=> //; by rewrite /F; case: pselect=> // hn; exfalso; exact: hn hcx.
  have hbound := @measure_indexed_cover R Y [the choiceType of (nat : Type)]
    beta hb (product_vertical_section S x) setT F (countableP setT) hcov.
  have he : nonnegative_sum setT (fun n => beta (F n)) = u x.
    apply: nonnegative_sum_ext=> n _; rewrite /F /f.
    case: pselect=> hn.
    + by rewrite (characteristic_on_set (ht n) hn) mule1.
    + by rewrite (characteristic_off_set (ht n) hn) mule0 (measure_empty hb).
  by rewrite -he.
Qed.
