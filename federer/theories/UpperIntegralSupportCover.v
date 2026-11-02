(** Federer (1969), 2.10.24, p. 188: supporting conversion of a finite upper
    integral to a countable finite-measure cover of the positive support.
    Choose a finite assigned upper step function from 2.4.2, p. 81, then use
    its positive finite-measure levels. Include the exceptional null set
    explicitly in the cover. No measurability of f or its positive support
    is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP
  MeasureStepFunctionUP MeasureIntegralUP MeasureIntegralBounds FiniteStepWeightedLevels WeightedLevelCoverBound NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_upper_integral_positive_support_cover]:
    supporting finite-measure support-cover reduction in
    2.10.24, p. 188. Positive levels of a finite
    upper step function cover outside a null exception;
    that exception itself has finite measure zero. *)
Theorem finite_upper_integral_positive_support_cover (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) :
  is_measure mu -> (forall x, 0<=f x) -> measure_upper_integral mu (partial_function_total f)< +oo ->
  exists A : nat -> set X, (forall n, mu (A n)< +oo) /\ [set x | 0<f x] `<=` \bigcup_n A n.
Proof.
move=> hm hf hfinite.
have [a [u [hu [hi ha]]]] : exists a u, is_measure_upper_function mu (partial_function_total f) u /\
    is_measure_step_integral mu u a /\ a< +oo.
  apply: contrapT=> hnone.
  have htop : +oo<=measure_upper_integral mu (partial_function_total f).
    apply: (measure_upper_integral_specification mu (partial_function_total f)).2=> a [u [hu hi]].
    rewrite leNgt; apply/negP=> ha; apply: hnone; exists a,u; split=> //; split.
  have hh := lt_le_trans hfinite htop; by rewrite ltxx in hh.
have [A [w [hw [hAfin [hsum hdom]]]]] := @finite_upper_step_weighted_levels R X mu f u a hm hf hu hi ha.
pose N := ~` [set x | f x<=weighted_level_sum A w x].
have hN : mu N=0 := hdom.
pose B n := if n is k.+1 then A k else N.
exists B; split.
- case=> [|n]; [rewrite /B hN; exact: ltry|exact: hAfin].
- move=> x hx.
  case: (pselect (N x))=> [hxN|hxN]; first by exists 0%N.
  have hgood : f x<=weighted_level_sum A w x by apply: contrapT=> hxg; exact: hxN hxg.
  have [n _ hxn] : (\bigcup_n A n) x.
    apply: contrapT=> hnone.
    have hz : weighted_level_sum A w x=0.
      apply: nonnegative_sum_zero=> n _.
      have hn : x \notin A n.
        apply/negP=> /set_mem hxA; apply: hnone; by exists n.
      by rewrite (negbTE hn).
    have hh := lt_le_trans hx hgood; by rewrite hz ltxx in hh.
  exists n.+1=> //.
Qed.
