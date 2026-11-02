(** Federer (1969), 2.3.8, p. 78: the possibly infinite pseudodistance and
    convergence in measure. Cauchy sequences appear in 2.3.10, p. 80. Source
    editions and partial-domain correction: MeasurableNormedFunctionUP.v.
    Membership in A(mu,Y) is a hypothesis of laws, not built into these
    relations. Extended distances are not silently coerced to a
    finite-valued metric structure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialNormedArithmetic MeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_normed_distance]: direct pseudodistance
    |f-g|_mu in Federer 2.3.8, p. 78, allowed to be
    infinite. The difference is defined on the common domain. *)
Definition measure_normed_distance (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f g : partial_function X V) :=
  measure_gauge mu N (partial_vector_subtract f g).

(** Source for [converges_in_measure]: direct convergence definition in
    Federer 2.3.8, p. 78, in epsilon form *)
Definition converges_in_measure (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R)
    (f : nat -> partial_function X V) (g : partial_function X V) :=
  forall e : R, (0 < e)%R -> exists K, forall n, (K <= n)%N ->
    measure_normed_distance mu N (f n) g < e%:E.

(** Source for [cauchy_in_measure]: supporting explicit Cauchy
    convention for the pseudometric of Federer 2.3.8, p. 78,
    used in the completeness assertion of 2.3.10, p. 80. *)
Definition cauchy_in_measure (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f : nat -> partial_function X V) :=
  forall e : R, (0 < e)%R -> exists K, forall n m,
    (K <= n)%N -> (K <= m)%N -> measure_normed_distance mu N (f n) (f m) < e%:E.
