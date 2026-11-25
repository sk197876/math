(** Federer (1969), 4.1.8, p. 361: the original
    almost-everywhere factor and product-density assertions.
    These supporting rules use only the original measurable
    rectangle bounds and coordinate measure bijection.
    Neither finite mass nor countable covers are added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureSplit
  MeasureFiniteClosure ProductMeasure MeasureBijectionUP MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_almost_everywhere_first_factor]:
    an original factor-conull assertion holds for almost
    every product pair, supporting Federer 4.1.8, p. 361,
    by 2.6.1, pp. 114–115. Zero times infinity is zero. *)
Lemma product_almost_everywhere_first_factor (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (ha:is_measure alpha) (hb:is_measure beta) (P:set X):
  measure_almost_everywhere alpha P ->
    measure_almost_everywhere (product_measure ha hb) [set z:X*Y|P z.1].
Proof.
move=>hP.
have hBound:=@product_measure_rectangle_bound R X Y alpha beta ha hb (~` P) setT
  (measure_null_measurable ha hP) (measure_measurable_whole hb).
rewrite hP mul0e in hBound.
rewrite /measure_almost_everywhere.
have hSet:~` [set z:X*Y|P z.1]=(~` P) `*` setT.
  apply/seteqP;split=>z hz;first by split.
  exact:hz.1.
rewrite hSet;apply/eqP;rewrite eq_le (measure_nonnegative (product_measure_is_measure ha hb)) andbT.
exact:hBound.
Qed.

(** Source for [product_almost_everywhere_second_factor]:
    the second original factor-conull assertion also lifts
    without a finiteness premise, supporting Federer 4.1.8,
    p. 361, by 2.6.1, pp. 114–115. *)
Lemma product_almost_everywhere_second_factor (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (ha:is_measure alpha) (hb:is_measure beta) (P:set Y):
  measure_almost_everywhere beta P ->
    measure_almost_everywhere (product_measure ha hb) [set z:X*Y|P z.2].
Proof.
move=>hP.
have hBound:=@product_measure_rectangle_bound R X Y alpha beta ha hb setT (~` P)
  (measure_measurable_whole ha) (measure_null_measurable hb hP).
rewrite hP mule0 in hBound.
rewrite /measure_almost_everywhere.
have hSet:~` [set z:X*Y|P z.2]=setT `*` (~` P).
  apply/seteqP;split=>z hz;first by split.
  exact:hz.2.
rewrite hSet;apply/eqP;rewrite eq_le (measure_nonnegative (product_measure_is_measure ha hb)) andbT.
exact:hBound.
Qed.

(** Source for [measure_bijection_almost_everywhere_iff]:
    the actual original coordinate identification preserves
    conull assertions in both directions, supporting Federer
    4.1.8, p. 361, by 2.4.18, p. 90. *)
Lemma measure_bijection_almost_everywhere_iff (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (nu:set Y->\bar R) (u:X->Y) (ui:Y->X)
    (hBij:is_measure_bijection mu nu u ui) (P:set Y):
  measure_almost_everywhere mu (u @^-1` P) <->measure_almost_everywhere nu P.
Proof.
rewrite /measure_almost_everywhere -(measure_bijection_pushforward hBij) /measure_pushforward
  preimage_setC;by [].
Qed.
