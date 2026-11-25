(** Federer (1969), 2.5.3, proof p. 95: reduction to finite positive
    combinations of characteristic functions, using the finite test sums of
    2.4.6, p. 84. We select a finite simple minorant by the integral's
    supremum law, then prove that each positive coefficient has
    finite-measure support. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureAlmostUP MeasureIntegralUP NonnegativeSum ExtendedRealBoundsUP
  FinitePositiveSimpleIntegralSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_positive_simple_minorant_supports_finite]: finiteness
    needed to apply the characteristic-function case in Federer 2.5.3, proof
    p. 95 Positive coefficients, together with summability of the majorant,
    force every selected support to have finite mass. *)
Lemma finite_positive_simple_minorant_supports_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (a : R) (C : {fset R}) (A : R -> set X) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu f a%:E -> is_positive_finite_simple_minorant mu f C A ->
  forall y, y \in C -> mu (A y) < +oo.
Proof.
move=> hp hi hC y hy.
have hs := @positive_finite_simple_integral_supremum R X mu hm f a%:E hp hi.
have hb : (\sum_(z <- C) z%:E*mu (A z)) <= a%:E.
  apply: (extended_real_supremum_upper hs); exists C,A; by split.
have hpos z : z \in C -> 0 <= z%:E*mu (A z).
  move=> hz; apply: mule_ge0; last exact: measure_nonnegative.
  rewrite lee_fin; exact: ltW (hC.2.2.1 z hz).
have hterm : y%:E*mu (A y) <= \sum_(z <- C) z%:E*mu (A z).
  rewrite -(nonnegative_sum_finite hpos).
  exact: (@nonnegative_sum_term R R [set z | z \in C] (fun z => z%:E*mu (A z)) y hy).
have hlt := le_lt_trans (le_trans hterm hb) (ltry a).
case he: (mu (A y))=> [r| |]; first exact: ltry.
- have hyE : (0 : \bar R) < y%:E by rewrite lte_fin; exact: hC.2.2.1 y hy.
  by move: hlt; rewrite he (gt0_muley hyE) ltxx.
- by rewrite ltNye.
Qed.

(** Source for [finite_positive_simple_integral_approximation]: quantitative
    finite-simple reduction for Federer 2.5.3, proof p. 95 The finite test
    integral is greater than integral(f)-delta and no greater than
    integral(f); all selected supports are finite. *)
Theorem finite_positive_simple_integral_approximation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (a d : R) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu f a%:E -> (0 < d)%R ->
  exists (C : {fset R}) (A : R -> set X) (b : R),
    is_positive_finite_simple_minorant mu f C A /\
    (forall y, y \in C -> mu (A y) < +oo) /\
    (\sum_(y <- C) y%:E*mu (A y))=b%:E /\ (a-d < b <= a)%R.
Proof.
move=> hp hi hd.
have hs := @positive_finite_simple_integral_supremum R X mu hm f a%:E hp hi.
have hex : exists c, positive_finite_simple_integral_values mu f c /\ (a-d)%R%:E < c.
  apply: contrapT=> hnone.
  have hb : a%:E <= (a-d)%R%:E.
    apply: (extended_real_supremum_least hs)=> c hc.
    rewrite leNgt; apply/negP=> hlt; apply: hnone; by exists c.
  have hl : (a-d)%R%:E < a%:E by rewrite lte_fin ltrBlDl ltrDr.
  by move: hl; rewrite ltNge hb.
have [c [hc hlow]] := hex.
have hup := extended_real_supremum_upper hs hc.
have hcf : c \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: (lt_trans (ltNyr _) hlow).
  - exact: le_lt_trans hup (ltry a).
have [C [A [hC heq]]] := hc.
exists C,A,(fine c); split=> //; split.
- exact: (@finite_positive_simple_minorant_supports_finite R X mu hm f a C A hp hi hC).
- split; first by rewrite -heq fineK.
  apply/andP; split; [move: hlow | move: hup]; by rewrite -(fineK hcf) ?lte_fin ?lee_fin.
Qed.
