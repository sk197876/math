(** Federer (1969), 3.1.19, p. 231: equivalence of all five
    submanifold descriptions. Every existence assertion is proved
    from the straightening definition or the constant-rank theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanSubmanifoldUP SubmanifoldChartsUP
  SubmanifoldStraighteningCoordinates SubmanifoldStraighteningLevelSets
  SubmanifoldCoordinateParametrisation SubmanifoldParametrisationStraightening
  SubmanifoldParametrisationGraph SubmanifoldOrthogonalCoordinates SubmanifoldLevelStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_1_19]: conditions (1) through (5) in
    Federer 3.1.19, p. 231, are equivalent for mu>=1 and k>=1.
    The auxiliary implication proofs also cover mu=0; the separate
    zero-dimensional theorem treats the printed final sentence. *)
Theorem federer_3_1_19 (R:realType) n mu k (B:set (R_n R n)) :
  (1<=mu)%N -> (1<=k)%N ->
  (@is_euclidean_submanifold R n mu k B <-> @has_regular_level_charts R n mu k B) /\
  (@is_euclidean_submanifold R n mu k B <-> @has_open_constant_rank_parametrisations R n mu k B) /\
  (@is_euclidean_submanifold R n mu k B <-> @has_convex_coordinate_charts R n mu k B) /\
  (@is_euclidean_submanifold R n mu k B <-> @has_orthogonal_graph_charts R n mu k B).
Proof.
move=>hmu hk.
have h14:=@submanifold_convex_coordinates R n mu k B.
have h43:=@convex_coordinates_open_parametrisations R n mu k B hk.
have h31:=@open_parametrisations_submanifold R n mu k B hk.
have h35:=@open_parametrisations_orthogonal_graphs R n mu k B hk.
have h54:=@orthogonal_graphs_convex_coordinates R n mu k B.
split.
- split; [exact: submanifold_regular_level_charts hk|exact: regular_level_charts_submanifold hk].
split.
- split; [move=>h; exact: h43 (h14 h)|exact h31].
split.
- split=>h; [exact: h14|exact: h31 (h43 h)].
split=>h; [exact: h35 (h43 (h14 h))|exact: h31 (h43 (h54 h))].
Qed.
