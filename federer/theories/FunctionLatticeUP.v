(** Federer (1969), 2.5.1, printed pp. 91–92: lattices of total finite
    real-valued functions. An empty lattice is permitted by the printed
    definition; zero membership is consequently derived only from a member. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [function_le]: direct pointwise ordering in Federer 2.5.1, p.
    91, first paragraph *)
Definition function_le (R : realType) (X : Type) (f g : X -> R) := forall x, f x <= g x.

(** Source for [function_nonnegative]: the pointwise sign condition defining
    L+ in Federer 2.5.1, p. 91 *)
Definition function_nonnegative (R : realType) (X : Type) (f : X -> R) := forall x, 0 <= f x.

(** Source for [is_function_lattice]: direct closure specification of
    Federer 2.5.1, p. 91 Real scalars are finite, and subtraction is
    required only for ordered pairs, exactly as printed. *)
Record is_function_lattice (R : realType) (X : Type) (L : set (X -> R)) : Prop := {
  (** Source for [function_lattice_add]: addition clause of Federer 2.5.1, p.
    91 *)
  function_lattice_add : forall f g, L f -> L g -> L (fun x => f x+g x);
  (** Source for [function_lattice_scale]: nonnegative scalar clause of
    Federer 2.5.1, p. 91 *)
  function_lattice_scale : forall c f, 0 <= c -> L f -> L (fun x => c * f x);
  (** Source for [function_lattice_minimum]: binary infimum clause of Federer
    2.5.1, p. 91 *)
  function_lattice_minimum : forall f g, L f -> L g -> L (fun x => Order.min (f x) (g x));
  (** Source for [function_lattice_truncation]: infimum with a nonnegative
    constant in Federer 2.5.1, p. 91 The constant itself need not belong to
    L. *)
  function_lattice_truncation : forall c f, 0 <= c -> L f -> L (fun x => Order.min (f x) c);
  (** Source for [function_lattice_ordered_difference]: ordered subtraction
    clause of Federer 2.5.1, p. 91 *)
  function_lattice_ordered_difference : forall f g, L f -> L g -> function_le f g -> L (fun x => g x-f x)
}.

(** Source for [positive_function_lattice]: direct definition of L+ in
    Federer 2.5.1, p. 91 *)
Definition positive_function_lattice (R : realType) (X : Type) (L : set (X -> R)) :=
  [set f | L f /\ function_nonnegative f].
