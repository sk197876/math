(** Federer (1969), 2.5.10, p. 101: the functional is defined on every H^1
    summable real function and bounded by its absolute integral. This
    supporting theorem transfers summability to a dominated Borel measure,
    using 2.2.3, p. 61, 2.3.3, p. 76, and 2.4.4(7)–(8), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedArithmetic PartialAbsolutePartsGraph MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureAbsoluteSummability SummableRealFunctionUP SummableRealArithmetic
  SummableCountableMeasurability CountablyMeasurableUP BorelRegularMeasureUP TopologicalBorel
  BorelDominatedFunctionTransfer BorelDominatedNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_dominated_real_absolute_integral]:
    supporting absolute-integral bound in Federer 2.5.10,
    p. 101. Both the original and dominated integrals
    are specified by their actual values; the result
    also provides summability for the original signed f. *)
Theorem borel_dominated_real_absolute_integral (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure mu) (f : X -> R) (a : R) :
  (forall B, borel_set B -> measure_measurable nu B) ->
  (forall B, nu B<=mu B) -> summable_real_functions mu f ->
  is_measure_integral mu (real_total_integrand (fun x => `|f x|%R)) a%:E ->
  summable_real_functions nu f /\ exists b : R,
    is_measure_integral nu (real_total_integrand (fun x => `|f x|%R)) b%:E /\ (b<=a)%R.
Proof.
move=> hb hd hs ha.
pose F := fun x : X => ((`|f x|%R)%:E : extended_real_line R).
have hi : is_measure_integral mu (partial_function_total F) a%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ ha)=> x z.
  exact: real_total_integrand_graph.
have hcs := @measure_summable_countably_measurable R X mu hm
  (partial_function_total F) (ex_intro _ a hi).
have he : partial_function_nonzero_locus (0 : extended_real_line R) (partial_function_total F)=
    [set x | F x<>0].
  apply/seteqP; split=> x.
  - move=> [z [hz hnz]]; change (F x<>0).
    by rewrite (hz : F x=z).
  - move=> hx; exists (F x); by split.
have hcount : measure_countably_measurable mu [set x | F x<>0].
  rewrite -he; exact: countably_measurable_function_locus hcs.
have hp x : 0<=F x by rewrite /F lee_fin normr_ge0.
have [b [hbi [hb0 hba]]] := @borel_dominated_nonnegative_integral R X mu nu hm hn hr
  F a%:E hb hd hp hcount hi.
have hfin : b \is a fin_num.
  rewrite (ge0_fin_numE hb0); exact: le_lt_trans hba (ltry a).
have habs : is_measure_integral nu (real_total_integrand (fun x => `|f x|%R)) (fine b)%:E.
  rewrite fineK //; apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ hbi)=> x z.
  symmetry; exact: real_total_integrand_graph.
have hmf := @borel_dominated_function_measurable R X (extended_real_line R) mu nu hm hn hr
  0 (real_total_integrand f) hb hd (@measure_summable_countably_measurable R X mu hm _ hs).
have habs' : is_measure_summable nu (partial_extended_function_absolute_value (real_total_integrand f)).
  exists (fine b); apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ habs)=> x z.
  rewrite real_total_integrand_graph; split.
  - move=> hz; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - move=> [y [hy <-]]; have hyE := (real_total_integrand_graph f x y).1 hy.
    by rewrite -hyE abse_EFin.
split.
- exact (@measure_absolute_summable_implies_summable R X nu hn _
    (countably_measurable_function_measurable hmf) habs').
- exists (fine b); split=> //; by move: hba; rewrite -(fineK hfin) lee_fin.
Qed.
