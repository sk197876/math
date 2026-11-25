(** Federer (1969), proof of 2.4.4(4), p. 83: the lower-bound half of
    additivity follows by negating upper- integral subadditivity. Source
    editions: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialFunctionGraphEquivalence PartialExtendedArithmetic PartialSumNegationGraph MeasureUP MeasureAlmostUP
  MeasureIntegralBounds MeasureIntegralNegation MeasureUpperIntegralSubadditive MeasureBoundGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lower_integral_sum_consequences]: supporting
    superadditivity and conull-domain result used in Federer
    2.4.4(4), p. 83. The defined lower-integral sum
    must exceed negative infinity; positive infinity is permitted. *)
Lemma measure_lower_integral_sum_consequences (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) z :
  extended_add (measure_lower_integral mu f) (measure_lower_integral mu g)=Some z -> -oo < z ->
  measure_almost_everywhere mu (partial_function_domain (partial_extended_function_add f g)) /\
  z <= measure_lower_integral mu (partial_extended_function_add f g).
Proof.
move=> hz hfin; have hn := extended_add_negated_sum hz.
rewrite (@measure_lower_integral_negation R X mu hm f)
  (@measure_lower_integral_negation R X mu hm g) !oppeK in hn.
have hnf : -z < +oo by rewrite lteNl.
have [hd hb] := @measure_upper_integral_sum_consequences R X mu hm
  (partial_extended_function_negate f) (partial_extended_function_negate g) (-z)%E hn hnf.
have hgraph := @partial_extended_sum_negation_graph R X f g.
split.
- have he := partial_function_equivalent_domains hgraph.
  rewrite /partial_extended_function_negate partial_function_postcompose_domain in he.
  by rewrite he.
- rewrite (@measure_lower_integral_negation R X mu hm).
  rewrite (@measure_upper_integral_graph_equivalent R X mu _ _ hgraph).
  by rewrite leeNr.
Qed.
