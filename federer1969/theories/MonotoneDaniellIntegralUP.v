(** Federer (1969), 2.5.1, p. 92, final paragraph, and the hypotheses of
    2.5.2, p. 92: additive, positively homogeneous, monotone,
    increasing-continuous integral functionals. The functional is
    represented on all real functions, but every law concerns only its
    restriction to L. This is a specification, not an axiom of existence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_functions_increase_to]: the pointwise
    increasing-convergence convention in Federer 2.5.1–2.5.2, p. 92 The
    limit is the supplied g *)
Definition real_functions_increase_to (R : realType) (X : Type)
    (f : nat -> X -> R) (g : X -> R) :=
  forall x, extended_increases_to (fun n => (f n x)%:E) (g x)%:E.

(** Source for [is_monotone_daniell_integral]: abstract specification of the
    four properties in Federer 2.5.1–2.5.2, p. 92 together with the additive
    lattice laws this is equivalent. The measure representation is proved
    separately in the development of 2.5.2. *)
Record is_monotone_daniell_integral (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) : Prop := {
  (** Source for [monotone_daniell_integral_add]: first display in Federer
    2.5.2, p. 92 *)
  monotone_daniell_integral_add : forall f g, L f -> L g -> A (fun x => (f x+g x)%R)=(A f+A g)%R;
  (** Source for [monotone_daniell_integral_scale]: second display in Federer
    2.5.2, p. 92 *)
  monotone_daniell_integral_scale : forall c f, (0 <= c)%R -> L f -> A (fun x => (c * f x)%R)=(c * A f)%R;
  (** Source for [monotone_daniell_integral_monotone]: third display in
    Federer 2.5.2, p. 92 *)
  monotone_daniell_integral_monotone : forall f g, L f -> L g -> function_le f g -> (A f <= A g)%R;
  (** Source for [monotone_daniell_integral_increases]: fourth display in
    Federer 2.5.2, p. 92 *)
  monotone_daniell_integral_increases : forall f g, (forall n, L (f n)) -> L g ->
    real_functions_increase_to f g -> extended_increases_to (fun n => (A (f n))%:E) (A g)%:E
}.
