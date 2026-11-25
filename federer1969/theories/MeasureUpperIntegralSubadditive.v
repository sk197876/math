(** Federer (1969), 2.4.3(6), p. 82: subadditivity when the sum of the upper
    integrals is defined and below positive infinity. The proof chooses
    upper step functions whose assigned sums contradict any proposed strict
    failure. Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialExtendedArithmetic
  MeasurableRealArithmetic MeasureUP MeasureAlmostUP MeasureStepFunctionUP MeasureStepAddition
  MeasureIntegralUP MeasureIntegralBounds MeasureFiniteUpperApproximant
  ExtendedRealSumUpperBounds MeasureUpperFunctionAddition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [defined_sum_below_infinity_summands]: supporting
    inference in Federer 2.4.3(6), p. 82: a defined sum
    below infinity has both summands below infinity. *)
Lemma defined_sum_below_infinity_summands (R : realType) (a b z : \bar R) :
  extended_add a b = Some z -> z < +oo -> a < +oo /\ b < +oo.
Proof.
case: a=> [a| |]; case: b=> [b| |];
  rewrite /extended_add /adde_def /= ?eqxx // => -[<-] hz;
  by split; rewrite ?ltry.
Qed.

(** Source for [measure_upper_integral_subadditive]: the
    inequality in Federer 2.4.3(6), p. 82. The explicit
    partial-sum premise excludes opposite infinities, as required
    by the book's arithmetic convention. The value may be -infinity. *)
Theorem measure_upper_integral_subadditive (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) z :
  extended_add (measure_upper_integral mu f) (measure_upper_integral mu g) = Some z ->
  z < +oo -> measure_upper_integral mu (partial_extended_function_add f g) <= z.
Proof.
move=> hz hfin; have [hf hg] := defined_sum_below_infinity_summands hz hfin.
rewrite leNgt; apply/negP=> hbad.
have he : measure_upper_integral mu f + measure_upper_integral mu g = z.
  by move: hz; rewrite /extended_add ltpinfty_adde_def // => -[].
have hsum : measure_upper_integral mu f + measure_upper_integral mu g <
    measure_upper_integral mu (partial_extended_function_add f g) by rewrite he.
have [r [s [hr [hs hrs]]]] := extended_sum_strict_real_upper_bounds hf hg hsum.
have [a [[u [hu ha]] har]] := @measure_upper_value_below R X mu f r%:E hr.
have [b [[v [hv hb]] hbs]] := @measure_upper_value_below R X mu g s%:E hs.
have haf : a < +oo := lt_trans har (ltry r).
have hbf : b < +oo := lt_trans hbs (ltry s).
have hab : extended_add a b = Some (a+b) by rewrite /extended_add ltpinfty_adde_def.
have huv := @measure_upper_function_add R X mu hm f g u v a b (a+b) hu hv ha hb hab.
have huvsum := @measure_step_integral_add R X mu hm u v a b (a+b) hu.1 hv.1 ha hb hab.
have hbound := @measure_upper_integral_bound R X mu (partial_extended_function_add f g)
  (partial_real_function_add u v) (a+b) huv huvsum.
have hstrict : a+b < measure_upper_integral mu (partial_extended_function_add f g).
  apply: lt_trans _ hrs; rewrite EFinD; exact: lteD har hbs.
by move: hstrict; rewrite ltNge hbound.
Qed.

(** Source for [measure_upper_integral_sum_consequences]: complete
    Federer 2.4.3(6), p. 82, together with the conull-
    domain fact explicitly checked in the first sentence of its proof. *)
Theorem measure_upper_integral_sum_consequences (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) z :
  extended_add (measure_upper_integral mu f) (measure_upper_integral mu g) = Some z -> z < +oo ->
  measure_almost_everywhere mu (partial_function_domain (partial_extended_function_add f g)) /\
  measure_upper_integral mu (partial_extended_function_add f g) <= z.
Proof.
move=> hz hfin; have [hf hg] := defined_sum_below_infinity_summands hz hfin.
split.
- exact (@finite_upper_integrals_sum_domain R X mu hm f g hf hg).
- exact (@measure_upper_integral_subadditive R X mu hm f g z hz hfin).
Qed.
