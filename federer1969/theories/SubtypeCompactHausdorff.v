(** General topology supporting Federer (1969), 2.5.15, pp. 108-109: the
    closed interval Y={y: -1<=y<=1} as a compact Hausdorff space, and a
    compact Hausdorff space is locally compact. A subset of a topological
    space carries the initial topology of its inclusion; compactness and
    separation are transported along the inclusion. These are background
    facts of general topology, in the sense of the standing conventions of
    Federer's Chapter 2. *)
From mathcomp Require Import all_boot boolp classical_sets functions topology subtype_topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_type_compact_whole]: supporting compactness of
    Y as a space in Federer 2.5.15, p. 108: a compact subset is a
    compact space in its induced topology. A proper filter on the
    subset pushes forward along the inclusion, and a cluster point of
    the image lies in the subset. *)
Lemma set_type_compact_whole (T : topologicalType) (A : set T) :
  compact A -> compact [set: set_type A].
Proof.
move=> hA F PF _.
pose G : set_system T := set_val @ F.
have PG : ProperFilter G by exact: fmap_proper_filter.
have hFT : F setT by exact: filterT.
have GA : G A by rewrite /G /fmap /=; move: hFT; apply: filterS=> y _; exact: set_valP.
have [x [hxA hx]] := hA G PG GA.
exists (exist _ x (mem_set hxA)); split=> //.
move=> B C hB; rewrite (@nbhsE (set_type A))=> -[W [[O hO <-] hWy] hWC].
have hGB : G (set_val @` B).
  by rewrite /G /fmap /=; move: hB; apply: filterS=> b hb; exists b.
have [t [himg hOt]] := hx _ _ hGB (open_nbhs_nbhs (conj hO hWy)).
have [b hb hbt] : exists2 b : set_type A, B b & set_val b = t by exact: himg.
by exists b; split=> //; apply: hWC; rewrite /= hbt.
Qed.

(** Source for [set_type_hausdorff]: supporting Hausdorff separation
    of Y as a space in Federer 2.5.15, p. 108: the induced topology
    of a subset of a Hausdorff space is Hausdorff. *)
Lemma set_type_hausdorff (T : topologicalType) (A : set T) :
  hausdorff_space T -> hausdorff_space (set_type A).
Proof.
move=> hT y z hyz; apply/val_inj; apply: hT=> B C hB hC.
have hcont : continuous (set_val : set_type A -> T) by exact: initial_continuous.
have [w [hwB hwC]] := hyz _ _ (hcont y B hB) (hcont z C hC).
by exists (set_val w).
Qed.

(** Source for [compact_space_locally_compact]: supporting local
    compactness of the compact space X=Y^J in Federer 2.5.15,
    p. 108, as required by the lattice of 2.5.13, p. 106: the whole
    space is a compact neighbourhood of each point. *)
Lemma compact_space_locally_compact (T : topologicalType) :
  compact [set: T] -> locally_compact [set: T].
Proof. by move=> hc x _; exists setT; [exact: filterT|]. Qed.
