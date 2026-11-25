(** Federer (1969), 3.2.20, p. 257: use the exact
    partial chain rule from 3.2.19 to describe the partial differential
    by an injective source chart, without extending its domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_linear_chart_graph]: supporting graph consequence
    of ap Df composed with Dpsi equals D(F composed with psi),
    Federer 3.2.19, p. 256, used in the Jacobian product of
    3.2.20, p. 257. The actual partial domain is the range
    of the source chart; no total inverse or off-domain values are assumed. *)
Theorem partial_linear_chart_graph (X Y Z : Type) (D : X -> Y) (H : X -> Z)
    (d : partial_function Y Z) :
  partial_function_domain d=range D ->
  partial_function_precompose D d=partial_function_total H ->
  forall v w, partial_function_graph d v w <-> exists x, D x=v /\ H x=w.
Proof.
move=> hDom hComp v w; split.
- move=> hvw; have hv : partial_function_domain d v by exists w.
  rewrite hDom in hv; have [x _ hx] := hv.
  have hh : partial_function_graph (partial_function_precompose D d) x w.
    change (partial_function_graph d (D x) w); by rewrite hx.
  rewrite hComp in hh; exists x; by split.
- move=> [x [hx hHw]].
  have hh : partial_function_graph (partial_function_precompose D d) x (H x).
    by rewrite hComp.
  change (partial_function_graph d (D x) (H x)) in hh.
  by rewrite hx hHw in hh.
Qed.
