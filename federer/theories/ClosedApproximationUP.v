(** Federer (1969), 2.2.2, p. 61: the class of sets admitting closed inner
    approximations for every positive error. Membership itself does not
    presume measurability of the approximated set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_closed_approximable]: Federer 2.2.2,
    p. 61, definition of the proof's class F: for every positive
    epsilon, A contains a closed C with mu(A minus C) below epsilon.
    It is a property, not a choice of a specific approximating sequence. *)
Definition is_closed_approximable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (A : set T) :=
  forall epsilon : R, (0 < epsilon)%R -> exists C,
    closed C /\ C `<=` A /\ mu (A `\` C) < epsilon%:E.

(** Source for [closed_set_approximable]: Federer 2.2.2,
    p. 61, the approximation class contains every closed set:
    choose that set itself, leaving empty error of measure zero. *)
Lemma closed_set_approximable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (A : set T) :
  closed A -> is_closed_approximable mu A.
Proof.
move=> hA epsilon he; exists A; split=> //; split; first by move=> x hx.
by rewrite setDv (measure_empty hm) lte_fin.
Qed.
