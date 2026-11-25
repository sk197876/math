(** Federer (1969), 3.2.35, p. 271:
    the corrected radial map has the original
    unit sphere as its exact partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RadialGaugeMapUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radial_gauge_map_domain]: supporting
    exact sphere domain of the boundary parametrization
    in Federer 3.2.35, p. 271, with
    erratum p. 5, book p. 271 line 24.
    The independent graph law proves both directions;
    no auxiliary values outside the sphere occur. *)
Lemma radial_gauge_map_domain (R:realType) (V:lmodType R)
    (N:V->R) (g:V->R) (f:partial_function V V):
  is_radial_gauge_map N g f ->partial_function_domain f=[set x|N x= 1].
Proof.
move=>hF; apply/seteqP; split=>x.
- move=>[y hy]; exact:((radial_gauge_map_graph_law hF x y).1 hy).1.
- move=>hx; exists ((g x)^-1*:x).
  apply:(radial_gauge_map_graph_law hF x _).2; by split.
Qed.
