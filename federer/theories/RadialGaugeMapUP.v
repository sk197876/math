(** Federer (1969), 3.2.35, p. 271:
    independent graph laws for the corrected
    partial radial map on the actual unit sphere.
    Apply erratum p. 5, book p. 271 line 24. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_radial_gauge_map]: the map
    x mapped to g(x)^(-1)x on the unit
    sphere in Federer 3.2.35, p. 271,
    corrected by erratum p. 5, book p. 271
    line 24. Its domain is exactly N(x)=1;
    there are no outside graph values. The laws
    precede the separate existence construction and
    do not assume any boundary image assertion. *)
Record is_radial_gauge_map (R:realType) (V:lmodType R)
    (N:V->R) (g:V->R) (f:partial_function V V):Prop:={
  radial_gauge_map_graph_law:forall x y,
    partial_function_graph f x y <->N x= 1 /\(g x)^-1*:x=y
}.
