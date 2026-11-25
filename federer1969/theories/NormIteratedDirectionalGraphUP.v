(** Federer (1969), 3.1.11, p. 223: the exact
    partial function specified by the recursive directional graph. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PartialFunctionUP NormIteratedDirectionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_norm_iterated_directional_graph]: the graph
    of the recursively defined ordered derivative, specializing to
    D_nu f in Federer 3.1.11, p. 223. Its domain is
    precisely the set of points where the recursive limits exist. *)
Definition is_norm_iterated_directional_graph (R : realType)
    (X Y : lmodType R) (NY : Y->R) (A : X->Prop) (f : X->Y)
    (s : seq X) (D : partial_function X Y) :=
  forall a y, partial_function_graph D a y <->
    has_norm_iterated_directional NY A f s a y.
