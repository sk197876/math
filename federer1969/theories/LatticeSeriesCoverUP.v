(** Federer (1969), 2.5.3, p. 94, third further condition: countable
    finite-measure covers and domination by a series of positive lattice
    functions. These are predicates, not extra axioms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_countably_finite_measure_set]: the left side of the third
    further condition in Federer 2.5.3, p. 94 The covering sets need not be
    measurable. *)
Definition is_countably_finite_measure_set (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (T : set X) :=
  exists F : set (set X), countable F /\ (forall B, F B -> mu B < +oo) /\
    T `<=` \bigcup_(B in F) B.

(** Source for [is_positive_lattice_series_cover]: the right side of the
    same condition in Federer 2.5.3, p. 94 Nonnegativity gives
    characteristic domination automatically outside T, so the explicit
    pointwise inequality is required only on T. The sum may be infinite. *)
Definition is_positive_lattice_series_cover (R : realType) (X : Type)
    (L : set (X -> R)) (T : set X) (f : nat -> X -> R) :=
  (forall n, positive_function_lattice L (f n)) /\
    forall x, T x -> 1 <= nonnegative_sum setT (fun n => (f n x)%:E).
