(** Federer (1969), 3.2.14, p. 252, first observation:
    S union T is m rectifiable when S and T are.
    Translate the second bounded parameter domain until
    it is separated from the first, then glue the graphs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialMetricLipschitz RectifiableSetUP
  PartialEuclideanTranslation EuclideanSeparatedParameters PartialSeparatedUnion
  CoveringFamilyUP MetricBoundedUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_union]: the assertion
    that S union T is m rectifiable, Federer 3.2.14,
    p. 252. Empty sets and the finite-set convention
    in dimension zero are included. *)
Theorem rectifiable_union (R : realType) (X : metricType R) m (E F : set X) :
  is_m_rectifiable m E -> is_m_rectifiable m F -> is_m_rectifiable m (E `|` F).
Proof.
case: m=> [|m].
  change (finite_set E -> finite_set F -> finite_set (E `|` F)).
  by rewrite finite_setU; move=> hE hF; split.
move=> [f [hf [[L hL] hrE]]] [g [hg [[M hM] hrF]]].
have hm : (0<m.+1)%N by [].
have [v hsep] := euclidean_bounded_parameters_separate hm hf hg.
have [g' htrans] := partial_euclidean_translation_exists g v.
have hg'b := partial_euclidean_translation_bounded htrans hg.
have hg'L := partial_euclidean_translation_lipschitz htrans hM.
have hs x y : partial_function_domain f x -> partial_function_domain g' y -> 1<=mdist x y.
  move=> hx [b hy]; apply: hsep=> //; exists b; exact: (htrans y b).1 hy.
have [h [hdom [hrange [C hC]]]] := partial_separated_union_exists
  hL hg'L hf hg'b ltr01 hs.
exists h; split.
- rewrite hdom; exact: metric_bounded_union hf hg'b.
- split; first by exists C.
  by rewrite hrange (partial_euclidean_translation_range htrans) hrE hrF.
Qed.
