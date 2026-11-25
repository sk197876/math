(** Federer (1969), 2.6.4, pp. 118–119: supporting finite-factor reduction
    of the rectangular covers used for density. Rectangles of finite
    positive cost have finite factor measures; every remaining rectangle has
    product measure zero. Removing their countable union therefore changes
    the cover only on a null set. This supporting reduction does not assert
    that a null rectangle admits a countable cover by rectangles with finite
    factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic
  ProductMeasure ProductRectangleValue NonnegativeSum FinitePositiveProductFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_finite_factor_cover]: supporting removal
    of null rectangles before the finite-union density step of
    Federer 2.6.4, pp. 118–119. The resulting rectangle
    union agrees with the original union up to an explicitly null
    set and has no larger covering cost. *)
Theorem product_finite_factor_cover (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (A : nat -> set X) (B : nat -> set Y) :
  (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) ->
  nonnegative_sum setT (fun n => alpha (A n)*beta (B n)) < +oo ->
  exists (C : nat -> set X) (D : nat -> set Y) (N : set (X*Y)),
    (forall n, measure_measurable alpha (C n) /\ alpha (C n) < +oo /\
      measure_measurable beta (D n) /\ beta (D n) < +oo) /\
    product_measure ha hb N = 0 /\
    (\bigcup_n (A n `*` B n)) = (\bigcup_n (C n `*` D n)) `|` N /\
    nonnegative_sum setT (fun n => alpha (C n)*beta (D n)) <=
      nonnegative_sum setT (fun n => alpha (A n)*beta (B n)).
Proof.
move=> hAB hs.
pose good n := (alpha (A n) < +oo /\ beta (B n) < +oo).
pose C n := if pselect (good n) then A n else set0.
pose D n := if pselect (good n) then B n else set0.
pose E n := if pselect (good n) then set0 else A n `*` B n.
have hCD n : measure_measurable alpha (C n) /\ alpha (C n) < +oo /\
    measure_measurable beta (D n) /\ beta (D n) < +oo.
  rewrite /C /D; case: (pselect (good n))=> hn.
  - split; first exact: (hAB n).1.
    split; first exact: hn.1.
    by split; [exact: (hAB n).2|exact: hn.2].
  - rewrite (measure_empty ha) (measure_empty hb); split; first exact: measure_measurable_empty ha.
    split; first exact: ltry.
    split; [exact: measure_measurable_empty hb|exact: ltry].
have hE n : product_measure ha hb (E n)=0.
  rewrite /E; case: (pselect (good n))=> hn; first exact: measure_empty (product_measure_is_measure ha hb).
  rewrite (product_measure_rectangle_value ha hb (hAB n).1 (hAB n).2).
  apply/eqP; rewrite eq_le (mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _)) andbT leNgt.
  apply/negP=> hp; apply: hn.
  have hf : alpha (A n)*beta (B n) < +oo.
    exact (le_lt_trans (@nonnegative_sum_term R [the choiceType of (nat : Type)] setT
      (fun k => alpha (A k)*beta (B k)) n I) hs).
  have hh := positive_finite_product_factors (measure_nonnegative ha (A n)) (measure_nonnegative hb (B n)) hp hf.
  by split; [exact: hh.2.1|exact: hh.2.2.2].
exists C,D,(\bigcup_n E n); split; first exact hCD.
split.
- exact (@measure_null_countable_union R (Choice.clone (X*Y)%type _) [the choiceType of (nat : Type)]
    _ (product_measure_is_measure ha hb) setT E (countableP setT) (fun n _ => hE n)).
split.
- apply/seteqP; split.
  + move=> p [n _ hp]; case hn: (pselect (good n))=> [hg|hg].
    * left; exists n=> //; by rewrite /C /D hn.
    * right; exists n=> //; by rewrite /E hn.
  + move=> p [[n _ hp]|[n _ hp]].
    * exists n=> //; move: hp; rewrite /C /D; case: (pselect (good n))=> hn //; by move=> [[] _].
    * exists n=> //; move: hp; rewrite /E; by case: (pselect (good n)).
- apply: nonnegative_sum_mono=> n _; rewrite /C /D; case: (pselect (good n))=> hn; first exact: lexx.
  rewrite (measure_empty ha) mul0e; exact: mule_ge0 (measure_nonnegative ha _) (measure_nonnegative hb _).
Qed.
