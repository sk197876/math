(** Federer (1969), proof of 2.4.3(6), p. 82: adding upper step functions,
    and the conull domain of f+g. Source context:
    PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBinaryOperation PartialExtendedArithmetic MeasurableRealArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureStepFunctionUP MeasureStepAddition
  MeasureIntegralUP MeasureIntegralBounds MeasureFiniteUpperApproximant PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_upper_integrals_sum_domain]: supporting
    first sentence of the proof of Federer 2.4.3(6), p. 82:
    f+g is defined almost everywhere when both upper integrals
    are below positive infinity. *)
Lemma finite_upper_integrals_sum_domain (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  measure_upper_integral mu f < +oo -> measure_upper_integral mu g < +oo ->
  measure_almost_everywhere mu (partial_function_domain (partial_extended_function_add f g)).
Proof.
move=> hf hg.
have hfg := @measure_almost_everywhere_and R X mu hm _ _
  (@finite_upper_integral_below_infinity_almost R X mu hm f hf)
  (@finite_upper_integral_below_infinity_almost R X mu hm g hg).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfg).
move=> x [[a [ha haf]] [b [hb hbf]]].
exists (a+b); apply/partial_extended_function_add_graph; exists a,b; split=> //; split=> //.
by rewrite /extended_add ltpinfty_adde_def.
Qed.

(** Source for [measure_upper_function_add]: the sum of upper
    step functions is an upper function for f+g when its assigned
    sum is defined, as used in Federer 2.4.3(6), p. 82.
    Upper functions already bound f,g by finite pointwise values,
    so no extra pointwise-domain assumption is needed. *)
Lemma measure_upper_function_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) u v a b z :
  is_measure_upper_function mu f u -> is_measure_upper_function mu g v ->
  is_measure_step_integral mu u a -> is_measure_step_integral mu v b ->
  extended_add a b = Some z ->
  is_measure_upper_function mu (partial_extended_function_add f g) (partial_real_function_add u v).
Proof.
move=> [hu hlu] [hv hlv] ha hb hz; split.
- exact (@measure_step_function_add R X mu hm u v a b z hu hv ha hb hz).
- have hfg := @measure_almost_everywhere_and R X mu hm _ _ hlu hlv.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfg).
  move=> x [[r [a' [hr [ha' har]]]] [s [b' [hs [hb' hbs]]]]].
  have haf : a' < +oo := le_lt_trans har (ltry r).
  have hbf : b' < +oo := le_lt_trans hbs (ltry s).
  exists (r+s)%R,(a'+b'); split.
  + exists (r,s); by split; [split|].
  split.
  + apply/partial_extended_function_add_graph; exists a',b'; split=> //; split=> //.
    by rewrite /extended_add ltpinfty_adde_def.
  + rewrite EFinD; exact: leeD har hbs.
Qed.
