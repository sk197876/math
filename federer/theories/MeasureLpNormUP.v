(** Federer (1969), 2.4.12, p. 86: the finite-p integral-root formula. These
    modules retain the possibly infinite value and exact partial domain. The
    abstract specification precedes its witness and sealed interface.
    Seminorm and completeness laws are separate results, not assumptions
    included in this specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialNormPower ExtendedPositivePower MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_lp_norm]: abstract finite-p definition
    in Federer 2.4.12, p. 86. The integral is specified
    by its upper/lower laws, and a is its positive p-th root.
    Measurability and existence of that integral are part of the
    assertion; no unproved seminorm axiom is introduced. *)
Definition is_measure_lp_norm (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (p : R) (f : partial_function X Y) a :=
  (1 <= p)%R /\ exists b, is_measure_integral mu (partial_norm_power N p f) b /\
    a = extended_positive_power b p^-1.

(** Source for [measure_lp_norm_unique]: uniqueness of the
    finite-p norm value specified in Federer 2.4.12, p. 86. *)
Lemma measure_lp_norm_unique (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (p : R) (f : partial_function X Y) a b :
  is_measure_lp_norm mu N p f a -> is_measure_lp_norm mu N p f b -> a=b.
Proof.
move=> [_ [u [hu ->]]] [_ [v [hv ->]]].
by rewrite (measure_integral_unique hu hv).
Qed.
