(** Federer (1969), 3.1.24, p. 240: analytic maps replace
    maps of class k in all five conditions of 3.1.19, p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations AnalyticSubmanifoldUP AnalyticSubmanifoldChartsUP
  AnalyticSubmanifoldCoordinates AnalyticSubmanifoldLevelSets AnalyticCoordinateParametrisation
  AnalyticParametrisationStraightening AnalyticParametrisationGraph AnalyticOrthogonalCoordinates
  AnalyticLevelStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [federer_3_1_19_analytic]: all five analytic
    submanifold conditions are equivalent, Federer 3.1.24, p. 240,
    referring to 3.1.19, p. 231. Each map's analyticity is
    proved from analytic linear maps, arithmetic, composition and
    inversion. This also covers dimension zero and empty subsets. *)
Theorem federer_3_1_19_analytic (R:realType) n mu (B:set (R_n R n)) :
  (@is_euclidean_analytic_submanifold R n mu B <-> @has_analytic_regular_level_charts R n mu B) /\
  (@is_euclidean_analytic_submanifold R n mu B <-> @has_analytic_open_parametrisations R n mu B) /\
  (@is_euclidean_analytic_submanifold R n mu B <-> @has_analytic_convex_coordinates R n mu B) /\
  (@is_euclidean_analytic_submanifold R n mu B <-> @has_analytic_orthogonal_graphs R n mu B).
Proof.
have h14:=@analytic_submanifold_convex_coordinates R n mu B.
have h43:=@analytic_convex_coordinates_open_parametrisations R n mu B.
have h31:=@analytic_open_parametrisations_submanifold R n mu B.
have h35:=@analytic_open_parametrisations_orthogonal_graphs R n mu B.
have h54:=@analytic_orthogonal_graphs_convex_coordinates R n mu B.
split.
- split; [exact: analytic_submanifold_regular_level_charts|exact: analytic_regular_level_charts_submanifold].
split.
- split; [move=>h; exact: h43 (h14 h)|exact h31].
split.
- split=>h; [exact: h14|exact: h31 (h43 h)].
split=>h; [exact: h35 (h43 (h14 h))|exact: h31 (h43 (h54 h))].
Qed.
