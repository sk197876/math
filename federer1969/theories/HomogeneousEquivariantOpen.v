(** Federer (1969), 3.2.28(2), printed p. 265: openness
    of the oriented Grassmann map follows from the actual
    homogeneous-space orbit laws of 2.7.1, p. 121. The
    erratum, book p. 265 line 3, deletes the printed
    phrase attributing this conclusion simply to compactness. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP HomogeneousSpaceUP HomogeneousSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [homogeneous_equivariant_open_map]: the
    open-map argument for Q in Federer 3.2.28(2), p. 265,
    through the open onto orbits of 2.7.1, p. 121.
    No compactness premise replaces the orbit laws. *)
Theorem homogeneous_equivariant_open_map (G X Y:topologicalType)
    (mul:G->G->G) (A:G->X->X) (B:G->Y->Y) (f:X->Y) (x:X):
  is_homogeneous_space mul A ->is_homogeneous_space mul B ->
  (forall g z,f (A g z)= B g (f z)) ->is_open_map f.
Proof.
move=>hA hB hEq U hU.
pose V:= [set g|U (A g x)].
have hV:open V.
  exact:(@open_comp G X (orbit_map A x) U
    (fun g _=>orbit_map_continuous hA x g) hU).
have hImage:orbit_map B (f x) @` V= f @` U.
  apply/seteqP; split=>y.
  - move=>[g hg <-]; exists (A g x)=>//; exact:hEq.
  - move=>[z hz <-].
    have hOnto: (orbit_map A x @` setT) z.
      by rewrite (homogeneous_orbit_onto hA x).
    have [g _ hg]:=hOnto.
    exists g; first by change (U (orbit_map A x g)); rewrite hg.
    by rewrite /orbit_map -(hEq g x) -hg.
rewrite -hImage; exact:(homogeneous_orbit_open hB (f x) hV).
Qed.
