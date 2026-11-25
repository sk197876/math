(** Federer (1969), 2.5.10, pp. 100–101: the disjoint finite-measure
    decomposition replacing countable measurability of X. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_sets_countably_covered]: the covering clause
    of Federer 2.5.10, pp. 100–101 Test sets need not be measurable, and
    their countable covers are required only up to a null remainder. *)
Definition finite_measure_sets_countably_covered (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (D : set J) (B : J -> set X) :=
  forall T, mu T < +oo -> exists C : set J,
    C `<=` D /\ countable C /\ mu (T `\` \bigcup_(j in C) B j)=0.

(** Source for [is_finite_measure_decomposition]: direct abstract condition
    in Federer 2.5.10, pp. 100–101 The full family need not be countable and
    its union need not equal the ambient space. *)
Definition is_finite_measure_decomposition (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (D : set J) (B : J -> set X) :=
  (forall j, D j -> measure_measurable mu (B j) /\ mu (B j) < +oo) /\
  (forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) /\
  finite_measure_sets_countably_covered mu D B.
