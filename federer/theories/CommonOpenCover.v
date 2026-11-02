(** Federer (1969), 2.10.1, p. 170: common refinements in the corrected
    arbitrary-topological construction. The common cover by intersections is
    elementary topology. It permits independent cover constraints before
    passing to the supremum, and supports measurability of continuous maps
    into metric spaces. Source context and corrected convention:
    TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import OpenRefiningEnvelopeUP TopologicalCaratheodoryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [common_open_cover]: supporting common
    refinement for the alternative construction in Federer
    2.10.1, p. 170. Intersect one member of each family. *)
Definition common_open_cover (X : Type) (H K : set (set X)) :=
  [set U | exists V W, H V /\ K W /\ U=V `&` W].

(** Source for [common_open_cover_whole]: supporting
    whole-space open-cover law for the corrected topological
    extension of Federer 2.10.1, p. 170. *)
Lemma common_open_cover_whole (X : topologicalType) (H K : set (set X)) :
  is_whole_space_open_cover H -> is_whole_space_open_cover K ->
  is_whole_space_open_cover (common_open_cover H K).
Proof.
move=> [hHo hHc] [hKo hKc]; split.
- move=> U [V [W [hV [hW ->]]]]; exact: openI (hHo V hV) (hKo W hW).
- move=> x _; have [V hV hxV] := hHc x I; have [W hW hxW] := hKc x I.
  exists (V `&` W); first by exists V,W.
  by split.
Qed.

(** Source for [generator_common_cover_left]: supporting
    inheritance of the first cover constraint in the
    corrected topological proof of Federer 2.10.1, p. 170. *)
Lemma generator_common_cover_left (X J : Type) (S : J -> set X)
    (H K : set (set X)) j :
  generator_refines_cover S (common_open_cover H K) j -> generator_refines_cover S H j.
Proof.
move=> [U [[V [W [hV [hW ->]]]] hSU]].
exists V; split=> // x hx; exact: (hSU x hx).1.
Qed.

(** Source for [generator_common_cover_right]: supporting
    inheritance of the second cover constraint in the
    corrected topological proof of Federer 2.10.1, p. 170. *)
Lemma generator_common_cover_right (X J : Type) (S : J -> set X)
    (H K : set (set X)) j :
  generator_refines_cover S (common_open_cover H K) j -> generator_refines_cover S K j.
Proof.
move=> [U [[V [W [hV [hW ->]]]] hSU]].
exists W; split=> // x hx; exact: (hSU x hx).2.
Qed.
