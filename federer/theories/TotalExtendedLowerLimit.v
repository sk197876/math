(** Federer (1969), 2.5.7, pp. 98–99: the increasing limit of candidate
    densities may initially take infinity. This supporting total-function
    adapter uses only the already sealed scalar lower-limit specification
    and the measurable lower-limit theorem from 2.3.2, p. 74. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionLimitExtremaUP
  ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit ExtendedRealOrderLimit ExtendedIncreasingLowerLimit
  MeasureUP MeasurableFunctionUP MeasurableLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_extended_lower_limit]: the pointwise lower limit used
    in Federer 2.5.7, pp. 98–99 This composes the existing sealed scalar
    operation, retaining both infinite values. *)
Definition total_extended_lower_limit (R : realType) (X : Type)
    (f : nat -> X -> extended_real_line R) (x : X) : extended_real_line R :=
  extended_lower_limit (fun n => f n x).

(** Source for [total_extended_lower_limit_specification]: supporting
    identification with the abstract partial lower limit of 2.3.2, p. 74,
    for the total functions in Federer 2.5.7, pp. 98–99 *)
Lemma total_extended_lower_limit_specification (R : realType) (X : Type)
    (f : nat -> X -> extended_real_line R) :
  is_partial_function_lower_limit (fun n => partial_function_total (f n))
    (partial_function_total (total_extended_lower_limit f)).
Proof.
constructor.
- apply/seteqP; split=> x hx.
  + exists 0%N=> n _; exists (f n x); by [].
  + exists (total_extended_lower_limit f x); by [].
- move=> x y hy b [K hK].
  have he : total_extended_lower_limit f x=y := hy; rewrite -he.
  apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws (fun n => f n x))).
  exists K=> n hn; exact: hK n hn (f n x) erefl.
- move=> x y hy b hb.
  have he : total_extended_lower_limit f x=y := hy; rewrite -he.
  apply: (extended_real_supremum_least (extended_lower_limit_laws (fun n => f n x)))=> c [K hK].
  apply: hb; exists K=> n hn z hz.
  have hez : f n x=z := hz; rewrite -hez; exact: hK n hn.
Qed.

(** Source for [total_extended_lower_limit_measurable]: supporting
    measurable limit in Federer 2.5.7, p. 98 No finite-value conclusion is
    assumed here. *)
Lemma total_extended_lower_limit_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> extended_real_line R) :
  (forall n, is_measure_measurable_function mu (partial_function_total (f n))) ->
  is_measure_measurable_function mu (partial_function_total (total_extended_lower_limit f)).
Proof.
move=> hf; exact: (@measurable_partial_lower_limit R X mu hm
  (fun n => partial_function_total (f n)) _ hf (total_extended_lower_limit_specification f)).
Qed.

(** Source for [total_extended_lower_limit_increases]: supporting pointwise
    increasing convergence in Federer 2.5.7, p. 98 Infinity remains a
    possible limit until a separate norm argument excludes it almost
    everywhere. *)
Lemma total_extended_lower_limit_increases (R : realType) (X : Type)
    (f : nat -> X -> extended_real_line R) :
  (forall n m x, (n <= m)%N -> f n x <= f m x) ->
  forall x, extended_increases_to (fun n => f n x) (total_extended_lower_limit f x).
Proof.
move=> hf x; exact: (@extended_increasing_lower_limit R (fun n => f n x)
  (total_extended_lower_limit f x) (fun n m hnm => hf n m x hnm) (extended_lower_limit_laws _)).
Qed.

(** Source for [total_extended_lower_limit_nonnegative]: positivity of the
    increasing candidate limit in Federer 2.5.7, p. 98 In fact nonnegative
    terms suffice without monotonicity for this supporting lemma. *)
Lemma total_extended_lower_limit_nonnegative (R : realType) (X : Type)
    (f : nat -> X -> extended_real_line R) :
  (forall n x, 0 <= f n x) -> forall x, 0 <= total_extended_lower_limit f x.
Proof.
move=> hf x; apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws (fun n => f n x))).
exists 0%N=> n _; exact: hf n x.
Qed.
