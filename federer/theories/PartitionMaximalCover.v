(** The maximal-cell argument in Federer (1969), 2.8.19, p. 152. Existence
    of the selected family is proved opaquely; downstream proofs use only
    its subfamily, countability, disjointness and union laws. No
    maximal-principle assumption or external covering theorem is used.
    Source comparison: RefiningBorelPartitionsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality topology.
From Federer Require Import CountablyClosedFamilyUP RefiningBorelPartitionsUP RefiningPartitionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partition_earliest_cell_at]: the existence of a maximal
    member containing each covered point in Federer 2.8.19, p. 152 The least
    level containing an eligible cell through x supplies a cell containing
    every eligible cell through x. *)
Lemma partition_earliest_cell_at (X : topologicalType) (P : nat -> set (set X))
    (F : set (set X)) x :
  is_refining_borel_partitions P -> F `<=` partition_levels_family P ->
  (\bigcup_(S in F) S) x ->
  exists S, F S /\ S x /\ forall T, F T -> T x -> T `<=` S.
Proof.
move=> hp hF [T hT hxT].
pose Q n := `[< exists S, P n S /\ F S /\ S x >].
have hQ : exists n, Q n.
  have [n _ hn] := hF T hT; exists n; apply/asboolP; by exists T.
have [n /asboolP [S [hnS [hSF hxS]]] hmin] := @ex_minnP Q hQ.
exists S; split=> //; split=> // U hU hxU.
have [j _ hjU] := hF U hU.
have hjQ : Q j by apply/asboolP; exists U; split=> //; split.
have hnj := hmin j hjQ.
exact (@partition_finer_meeting_subset X P hp n j S U x hnj hnS hjU hxS hxU).
Qed.

(** Source for [partition_maximal_cell_at]: the pointwise maximal-member
    conclusion in Federer 2.8.19, p. 152, obtained. The maximality is among
    all eligible members for inclusion, rather than just the cells with a
    prescribed level. *)
Lemma partition_maximal_cell_at (X : topologicalType) (P : nat -> set (set X))
    (F : set (set X)) x :
  is_refining_borel_partitions P -> F `<=` partition_levels_family P ->
  (\bigcup_(S in F) S) x -> exists S, is_maximal_family_member F S /\ S x.
Proof.
move=> hp hF hx.
have [S [hS [hxS htop]]] := @partition_earliest_cell_at X P F x hp hF hx.
exists S; split=> //; split=> // T hT hST; exact: htop T hT (hST x hxS).
Qed.

(** Source for [partition_maximal_cells_disjoint]: distinct maximal members
    are disjoint in Federer 2.8.19, p. 152 Meeting partition cells are
    nested, so maximality forces equality. *)
Lemma partition_maximal_cells_disjoint (X : topologicalType) (P : nat -> set (set X))
    (F : set (set X)) :
  is_refining_borel_partitions P -> F `<=` partition_levels_family P ->
  set_family_disjoint [set S | is_maximal_family_member F S].
Proof.
move=> hp hF S T [hSF hSm] [hTF hTm] hne.
apply/seteqP; split=> [x [hxS hxT]|x []].
exfalso; apply: hne.
have [i _ hi] := hF S hSF; have [j _ hj] := hF T hTF.
case/orP: (leq_total i j)=> hij.
- have hTS := @partition_finer_meeting_subset X P hp i j S T x hij hi hj hxS hxT.
  apply/seteqP; split; first exact: hTm S hSF hTS.
  exact hTS.
- have hST := @partition_finer_meeting_subset X P hp j i T S x hij hj hi hxT hxS.
  apply/seteqP; split; first exact hST.
  exact: hSm T hTF hST.
Qed.

(** Source for [partition_maximal_subfamily_cover]: the exact disjoint
    covering of the union by maximal eligible cells in Federer 2.8.19, p.
    152 Countability follows from the countable union of Borel partition
    levels, even with empty eligible cells. *)
Theorem partition_maximal_subfamily_cover (X : topologicalType)
    (P : nat -> set (set X)) (F : set (set X)) :
  is_refining_borel_partitions P -> F `<=` partition_levels_family P ->
  exists G, G `<=` F /\ countable G /\ set_family_disjoint G /\
    (\bigcup_(S in G) S) = (\bigcup_(S in F) S).
Proof.
move=> hp hF.
pose G := [set S | is_maximal_family_member F S].
have hGF : G `<=` F by move=> S [].
exists G; split=> //; split.
- apply: sub_countable _ (partition_levels_countable hp).
  exact: subset_card_le (subset_trans hGF hF).
- split; first exact: partition_maximal_cells_disjoint hp hF.
  apply/seteqP; split.
  + move=> x [S hS hx]; exists S=> //; exact: hGF.
  + move=> x hx; have [S [hS hxS]] := @partition_maximal_cell_at X P F x hp hF hx.
    by exists S.
Qed.
