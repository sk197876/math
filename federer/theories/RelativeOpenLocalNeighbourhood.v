(** Federer (1969), 3.4.8(10), p. 332:
    local source neighbourhoods give relative
    openness of each ordered sheet. This
    elementary topology connection uses the
    interior of the local implication set. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_open_local_neighbourhood]:
    the local inverse images are relatively
    open subsets of Z in 3.4.8(10),
    p. 332. Each source point
    has an ambient neighbourhood whose points
    in Z stay in the given sheet. *)
Theorem relative_open_local_neighbourhood (X:topologicalType) (Z S:set X):
  S `<=` Z ->(forall x,S x ->nbhs x [set z|Z z ->S z]) ->
  relatively_open_set Z S.
Proof.
move=>hSZ hLocal.
pose A:set X:=fun z=>Z z ->S z.
exists (interior A);split;first exact:open_interior A.
apply/seteqP;split.
- move=>x hx;split;first exact:hSZ x hx.
  exact:hLocal x hx.
- move=>x [hx hInterior];exact:(interior_subset hInterior) hx.
Qed.
