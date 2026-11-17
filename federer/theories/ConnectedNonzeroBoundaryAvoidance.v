(** Federer (1969), 3.4.8(11), p. 333:
    a critical component with a positive
    constant value cannot cross the boundary
    of an original positive component. The
    boundary value of Psi is zero. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [connected_nonzero_boundary_avoidance]:
    the component of a critical maximum
    cannot meet the boundary of C,
    3.4.8(11), p. 333. This supporting
    topology lemma does not assume C open. *)
Theorem connected_nonzero_boundary_avoidance (X:topologicalType) (Y:zmodType)
    (B C:set X) (f:X->Y) a:
  connected B ->B a ->C a ->f a<>0 ->
  (forall x,B x ->f x = f a) ->
  (forall x,closure C x ->~interior C x ->f x = 0) ->
  B `<=` C.
Proof.
move=>hConnected hBa hCa hNonzero hConstant hBoundary.
have hInterior x (hBx:B x) (hClosure:closure C x):interior C x.
  apply:contrapT=>hNot;apply:hNonzero.
  rewrite -(hConstant x hBx);exact:hBoundary x hClosure hNot.
have hEqual:B `&` interior C = B `&` closure C.
  apply/seteqP;split.
  - move=>x [hx hCx];split;first exact:hx.
    exact:subset_closure (interior_subset hCx).
  - move=>x [hx hCx];split;[exact:hx|exact:hInterior x hx hCx].
have hWhole:B `&` interior C = B.
  apply:hConnected.
  - exists a;split;first exact:hBa.
    exact:hInterior a hBa (subset_closure hCa).
  - by exists (interior C);first exact:open_interior.
  - exists (closure C);first exact:closed_closure.
    exact:hEqual.
move=>x hx;have h:(B `&` interior C) x by rewrite hWhole.
exact:interior_subset h.2.
Qed.
