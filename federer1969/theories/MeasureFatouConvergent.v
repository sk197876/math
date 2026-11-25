(** Federer (1969), 2.4.12, p. 87: application of Fatou's lemma to a
    convergent sequence of nonnegative integrands. These supporting lemmas
    identify the sealed lower limit almost everywhere; no default values are
    assigned outside partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionLimitExtremaUP
  PartialFunctionLowerLimitSealed PartialDominatedConvergence PartialIncreasingLowerLimit
  ExtendedLowerLimitUP ExtendedLowerLimit ExtendedConvergentLowerLimit
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  PartialExtendedOrderLoci MeasureFatou.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_convergent_lower_limit_almost_equal]:
    supporting identification of the pointwise lower limit in
    the Fatou argument of Federer 2.4.12, p. 87.
    Convergence is only required almost everywhere. *)
Lemma partial_convergent_lower_limit_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g k : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f k ->
  measure_almost_everywhere mu (partial_extended_convergence_locus f g) ->
  measure_almost_equal mu g k.
Proof.
move=> hk he; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [z [hu [hz hl]]]].
have hd : partial_function_domain k x.
  rewrite (partial_function_lower_limit_domain hk); exists 0%N=> n _.
  by exists (u n).
have [y hy] := hd.
have hyl := @partial_lower_limit_scalar_values R X f k x u y hk hu hy.
have ey := extended_lower_limit_unique hyl (extended_convergent_lower_limit hl).
exists z; split=> //; by rewrite -ey.
Qed.

(** Source for [measure_fatou_convergent_values]: the convergent
    case of 2.4.6 used in Federer 2.4.12, p. 87,
    expressed with abstract integral values. Both the integrals
    and their lower limit may be infinite. *)
Lemma measure_fatou_convergent_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (a : nat -> \bar R) b :
  measure_almost_everywhere mu (partial_extended_convergence_locus f g) ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, is_measure_integral mu (f n) (a n)) ->
  is_measure_integral mu g b -> b <= extended_lower_limit a.
Proof.
move=> hl hp hi hg.
pose k := @PartialFunctionLowerLimit.value R X f.
have hk := @PartialFunctionLowerLimit.laws R X f.
have he := @partial_convergent_lower_limit_almost_equal R X mu hm f g k hk hl.
have hki := @measure_integral_almost_equal R X mu hm g k b hg he.
exact (@measure_fatou_integral_values R X mu hm f k a b hk hp hi hki).
Qed.
