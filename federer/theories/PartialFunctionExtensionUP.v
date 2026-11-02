(** Federer (1969), 2.3.2, p. 73, second paragraph: extension to a function
    on all of X. We specify extension by preservation of the original graph,
    before proving existence. A nonempty target suffices. Empty targets
    require separate care; the book's unqualified remark otherwise fails for
    a nonempty null source. This boundary is not an entry in Federer's
    erratum. *)
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_partial_function_total_extension]: supporting
    abstract specification of the extension in Federer 2.3.2,
    p. 73, second paragraph. This is a predicate to be proved,
    not an additional project axiom. *)
Definition is_partial_function_total_extension (X Y : Type)
    (f : partial_function X Y) (h : X -> Y) :=
  forall x y, partial_function_graph f x y -> h x = y.
