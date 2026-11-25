(** Federer (1969), 3.2.22, p. 259: the image
    of the actual partial approximate differential equals the
    image of its source-chart composite differential. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_linear_chart_image]: supporting
    im ap Df(psi(x))=im D(F composed with psi)(x)
    in Federer 3.2.22, p. 259. Exact partial
    graph laws give both inclusions without choosing
    ambient values outside the tangent plane. *)
Lemma partial_linear_chart_image (X Y Z:Type) (D:X->Y) (H:X->Z)
    (d:partial_function Y Z):
  (forall v w,partial_function_graph d v w <->exists x,D x=v /\ H x=w) ->
  [set w:Z|exists v:Y,partial_function_graph d v w]=range H.
Proof.
move=>hGraph; apply/seteqP; split=>w.
- move=>[v hvw]; have [x [hDx hHx]]:=(hGraph v w).1 hvw.
  by exists x.
- move=>[x _ hHx]; exists (D x).
  apply:(hGraph _ _).2; exists x; by split.
Qed.
