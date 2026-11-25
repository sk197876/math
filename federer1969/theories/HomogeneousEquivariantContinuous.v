(** Federer (1969), 3.3.1, p. 287: continuity of the
    kernel map follows from its equivariance and the homogeneous
    space laws of 2.7.1, p. 121. Supply the quotient argument
    explicitly; do not assume continuity in the kernel specification. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP HomogeneousSpaceUP HomogeneousSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [homogeneous_equivariant_continuous_map]:
    supporting the final sentence of Federer 3.3.1, p. 287,
    through the continuous open onto orbit maps of 2.7.1,
    p. 121. The inverse image of an open set is the open
    orbit image of its inverse image in the common acting group. *)
Theorem homogeneous_equivariant_continuous_map (G X Y:topologicalType)
    (mul:G->G->G) (A:G->X->X) (B:G->Y->Y) (f:X->Y) (x0:X):
  is_homogeneous_space mul A ->is_homogeneous_space mul B ->
  (forall g z,f (A g z)=B g (f z)) ->continuous f.
Proof.
move=>hA hB hEq; apply/continuousP=>U hU.
pose V:=[set g|U (B g (f x0))].
have hV:open V.
  exact:((continuousP (orbit_map B (f x0))).1 (orbit_map_continuous hB (f x0)) U hU).
have hImage:(orbit_map A x0) @` V=f @^-1` U.
  apply/seteqP; split=>y.
  - move=>[g hg <-]; change (U (f (A g x0))).
    by rewrite hEq.
  - move=>hy.
    have hOnto:(orbit_map A x0 @` setT) y.
      by rewrite (homogeneous_orbit_onto hA x0).
    have [g _ hg]:=hOnto.
    exists g; last exact:hg.
    change (U (B g (f x0))); rewrite -hEq.
    change (U (f (orbit_map A x0 g))); by rewrite hg.
rewrite -hImage; exact:(homogeneous_orbit_open hA x0 hV).
Qed.
