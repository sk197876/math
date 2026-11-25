(** Federer (1969), 2.5.7, p. 98: Fatou's lemma bounds the positive power of
    the increasing candidate limit. These supporting pointwise identities
    use the sealed scalar lower limit and the proved interchange with
    positive powers. Infinity is retained; no finite projection is used in
    these identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionLimitExtremaUP
  ExtendedLowerLimitUP ExtendedLowerLimit ExtendedPositivePower ExtendedPositivePowerLowerLimit TotalExtendedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_lower_limit_positive_power]: supporting pointwise
    power interchange for the Fatou step in Federer 2.5.7, p. 98 Nonnegative
    terms and a strictly positive exponent are explicit hypotheses. *)
Lemma total_lower_limit_positive_power (R : realType) (X : Type)
    (f : nat -> X -> extended_real_line R) (p : R) :
  (forall n x, 0 <= f n x) -> (0 < p)%R -> forall x,
  extended_positive_power (total_extended_lower_limit f x) p=
    total_extended_lower_limit (fun n x => extended_positive_power (f n x) p) x.
Proof.
move=> hf hp x.
exact: (@extended_lower_limit_unique R (fun n => extended_positive_power (f n x) p) _ _
  (@extended_positive_power_lower_limit R (fun n => f n x) (total_extended_lower_limit f x) p
    (fun n => hf n x) hp (extended_lower_limit_laws _)) (extended_lower_limit_laws _)).
Qed.

(** Source for [total_lower_limit_power_specification]: supporting
    partial-graph lower-limit law needed to apply Fatou in Federer 2.5.7, p.
    98 It is derived from scalar laws, independently of measurability. *)
Lemma total_lower_limit_power_specification (R : realType) (X : Type)
    (f : nat -> X -> extended_real_line R) (p : R) :
  (forall n x, 0 <= f n x) -> (0 < p)%R ->
  is_partial_function_lower_limit
    (fun n => partial_function_total (fun x => (extended_positive_power (f n x) p : extended_real_line R)))
    (partial_function_total (fun x => (extended_positive_power (total_extended_lower_limit f x) p : extended_real_line R))).
Proof.
move=> hf hp.
have he : (fun x => (extended_positive_power (total_extended_lower_limit f x) p : extended_real_line R))=
    total_extended_lower_limit (fun n x => extended_positive_power (f n x) p).
  apply: funext=> x; exact: (@total_lower_limit_positive_power R X f p hf hp x).
rewrite he; exact: total_extended_lower_limit_specification.
Qed.
