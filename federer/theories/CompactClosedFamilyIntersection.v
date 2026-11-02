(** Federer (1969), 2.10.43, printed p. 201: because the prescribed balls
    are compact, their common intersection is nonempty once every finite
    subfamily has nonempty intersection. This general topology lemma keeps
    one compact member and requires only closedness of the others. *)
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_closed_family_intersection]: supporting
    finite-intersection step in 2.10.43, p. 201.
    A nonempty indexed closed family with one compact
    member and nonempty finite intersections has nonempty
    total intersection. The finite subcover argument
    also covers an arbitrary, uncountable index family. *)
Theorem compact_closed_family_intersection (X : topologicalType) (J : choiceType)
    (D : set J) (C : J -> set X) (j0 : J) :
  D j0 -> compact (C j0) -> (forall j, D j -> closed (C j)) ->
  (forall F : {fset J}, (forall j, j \in F -> D j) ->
    exists x, forall j, j \in F -> C j x) ->
  exists x, forall j, D j -> C j x.
Proof.
move=> hj0 hcompact hclosed hfinite; apply: contrapT=> hnone.
have hcover : C j0 `<=` \bigcup_(j in D) ~` C j.
  move=> x hx; apply: contrapT=> hmiss; apply: hnone.
  exists x=> j hj; apply: contrapT=> hnot; apply: hmiss.
  by exists j.
have [F hFD hFcover] := @compact_open_finite_cover X J D (fun j=>~` C j) (C j0)
  hcompact (fun j hj=>closed_openC (hclosed j hj)) hcover.
have hD' j : j \in (j0 |` F)%fset -> D j.
  rewrite !inE=> /orP [/eqP ->|hj]; first exact hj0.
  exact: set_mem (hFD j hj).
have [x hx] := hfinite (j0 |` F)%fset hD'.
have hx0 : C j0 x := hx j0 ltac:(by rewrite !inE eqxx).
have [j hj hnot] := hFcover x hx0.
apply: hnot; apply: hx; by rewrite !inE hj orbT.
Qed.
