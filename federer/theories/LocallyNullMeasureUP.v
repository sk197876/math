(** Federer (1969), 2.5.14, p. 108: the representing density is only locally
    almost unique without hypothesis (3) of 2.5.12. This supporting
    finite-test formulation means that the exceptional set has null
    intersection with every finite-measure set. For Radon measures it is
    equivalent to testing compact sets, as proved separately using 2.5.10,
    p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_locally_null]: supporting finite-test
    expression of the local qualification in Federer 2.5.14,
    p. 108. Global measure zero is not part of this definition. *)
Definition measure_locally_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (N : set X) :=
  forall A, mu A < +oo -> mu (A `&` N)=0.

(** Source for [measure_locally_almost_everywhere]: supporting
    local almost-everywhere convention for Federer 2.5.14,
    p. 108, using the complement convention of 2.3.1, p. 72. *)
Definition measure_locally_almost_everywhere (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (P : set X) := measure_locally_null mu (~` P).
