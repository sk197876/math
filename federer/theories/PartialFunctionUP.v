(** Federer (1969), 2.3.1, p. 72, and 2.3.2, p. 73: functions may have
    domains smaller than the measured space. This general set-theoretic
    interface specifies a function by a single-valued graph; it does not
    assume a value outside its domain or an inhabited target. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function]: set-theoretic background for the
    functions in Federer 2.3.1, p. 72, and the domain convention in
    2.3.2, p. 73. The graph law asserts uniqueness of a value,
    without asserting that every source point has a value. *)
Record partial_function (X Y : Type) := {
  (** Source for [partial_function_graph]: the graph of the partial
      function used in Federer 2.3.1, p. 72; background notation. *)
  partial_function_graph : X -> Y -> Prop;
  (** Source for [partial_function_single_valued]: the function law
      implicit in Federer 2.3.1, p. 72; background specification. *)
  partial_function_single_valued : forall x y z,
    partial_function_graph x y -> partial_function_graph x z -> y = z
}.

(** Source for [partial_function_domain]: the domain appearing in
    Federer 2.3.2, p. 73: precisely the source points with a value. *)
Definition partial_function_domain (X Y : Type) (f : partial_function X Y) : set X :=
  [set x | exists y, partial_function_graph f x y].

(** Source for [partial_function_preimage]: inverse-image notation
    in Federer 2.3.2, p. 73. Undefined source points belong to no
    inverse image, including the inverse image of the whole target. *)
Definition partial_function_preimage (X Y : Type) (f : partial_function X Y)
    (A : set Y) : set X :=
  [set x | exists y, partial_function_graph f x y /\ A y].

(** Source for [partial_function_agreement]: the equality locus in
    Federer 2.3.1, p. 72. Both functions must be defined, with the
    same value. In particular two undefined values do not agree. *)
Definition partial_function_agreement (X Y : Type)
    (f g : partial_function X Y) : set X :=
  [set x | exists y, partial_function_graph f x y /\ partial_function_graph g x y].
