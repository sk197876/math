(** Federer (1969), 2.4.6, p. 84: the lower limit of a nonnegative
    measurable sequence is nonnegative almost everywhere and measurable. We
    retain the larger eventual domain from the existing lower-limit
    specification; the common domain is conull. Source context:
    ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionLimitExtremaUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasurableFunctionUP MeasurableLowerLimit MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lower_limit_nonnegative]: supporting first
    observation in the proof of Federer 2.4.6, p. 84 Nonnegativity is
    allowed almost everywhere, a null-set extension of the printed
    hypothesis. *)
Lemma measure_lower_limit_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f g ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus g).
Proof.
move=> hg hf.
have he := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n => partial_extended_nonnegative_locus (f n)) (countableP _) (fun n _ => hf n).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
have hd : partial_function_domain g x.
  rewrite (partial_function_lower_limit_domain hg); exists 0%N=> n _.
  have [y [hy _]] := hx n Logic.I; by exists y.
have [y hy] := hd; exists y; split=> //.
apply: (@partial_function_lower_limit_upper R X f g hg x y hy 0).
exists 0%N=> n _ z hz; have [w [hw hw0]] := hx n Logic.I.
have ez := partial_function_single_valued hw hz; by rewrite -ez.
Qed.

(** Source for [measure_lower_limit_nonnegative_integral]: the
    lower-limit function has an integral given by its lower
    integral, as used at the start of Federer 2.4.6,
    p. 84, by 2.4.4(2). *)
Lemma measure_lower_limit_nonnegative_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f g ->
  (forall n, is_measure_measurable_function mu (f n)) ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  is_measure_integral mu g (measure_lower_integral mu g) /\ 0 <= measure_lower_integral mu g.
Proof.
move=> hg hf hp; apply: (@nonnegative_measurable_function_integral R X mu hm g).
- exact (@measurable_partial_lower_limit R X mu hm f g hf hg).
- exact (@measure_lower_limit_nonnegative R X mu hm f g hg hp).
Qed.
