(** Federer (1969), 2.3.2, p. 74: upper limits of measurable numerical
    functions are measurable. *)
From mathcomp Require Import all_boot classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableAlmostModification
  PartialFunctionSupremumUP PartialFunctionInfimumUP PartialFunctionSupremumSealed
  PartialFunctionInfimumSealed PartialFunctionLimitExtremaUP PartialFunctionUpperLimitSealed
  PartialUpperLimitNested MeasurableCountableSupremum MeasurableCountableInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_partial_upper_limit]: direct upper-limit
    measurability assertion of Federer 2.3.2, p. 74, with the eventual
    domain explicit. *)
Theorem measurable_partial_upper_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  (forall n, is_measure_measurable_function mu (f n)) ->
  is_partial_function_upper_limit f g -> is_measure_measurable_function mu g.
Proof.
move=> hf hg.
pose s n := @PartialFunctionSupremum.value R X nat [set i | (n <= i)%N] f.
pose h := @PartialFunctionInfimum.value R X nat setT s.
have hsm n : is_measure_measurable_function mu (s n).
  apply: (@measurable_sealed_countable_supremum R X nat mu hm _ f (countableP _)).
  by move=> i _; exact: hf i.
have hhm : is_measure_measurable_function mu h.
  apply: (@measurable_sealed_countable_infimum R X nat mu hm setT s (countableP _)).
  by move=> n _; exact: hsm n.
apply: (@measurable_function_almost_equal R X (extended_real_line R) mu hm h g hhm).
apply: (@measure_almost_everywhere_mono R X mu hm (partial_function_common_domain setT f)).
- apply: (@partial_upper_limit_nested_agreement R X f s g h)=> //.
  + move=> n; exact: PartialFunctionSupremum.laws.
  + exact: PartialFunctionInfimum.laws.
- apply: (@measure_almost_everywhere_countable R X nat mu hm setT _ (countableP _)).
  move=> n _; exact: measurable_function_domain (hf n).
Qed.

(** Source for [measurable_sealed_upper_limit]: usable sealed
    upper-limit form of Federer 2.3.2, p. 74, on the
    eventual common domain, including infinite limit values. *)
Corollary measurable_sealed_upper_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R)) :
  (forall n, is_measure_measurable_function mu (f n)) ->
  is_measure_measurable_function mu (@PartialFunctionUpperLimit.value R X f).
Proof.
move=> hf; exact: (@measurable_partial_upper_limit R X mu hm f _ hf
  (@PartialFunctionUpperLimit.laws R X f)).
Qed.
