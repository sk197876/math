(** Federer (1969), 2.10.30, p. 195: Steiner symmetrisation preserves
    containment in a closed ball centred at zero. This proof uses the
    abstract section laws and Pythagoras, never the existence construction.
    Source context: NormalBallSections.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric OrthonormalFamilies UnitNormalGeometry
  NormalBallSections SteinerSymmetrisationUP SteinerSymmetrisationLaws
  CenteredSectionUP CenteredSectionBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_preserves_centered_ball]: direct
    T contained in the closed B(0,r) assertion
    of 2.10.30, p. 195. Compactness of
    S is unnecessary for this containment alone;
    the separate boundary conclusion uses it. *)
Theorem steiner_preserves_centered_ball (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set V) (r : R) :
  is_steiner_symmetrisation hB u S T -> 0<=r ->
  (forall x, S x -> inner_norm hB x<=r) ->
  forall x, T x -> inner_norm hB x<=r.
Proof.
move=> hT hr hS x hx.
pose y := normal_foot hB u x.
pose t := inner_coordinate hB u x.
have hu := steiner_unit_normal_law hT.
have hy : inner_coordinate hB u y=0 := normal_coordinate_foot hB hu x.
have hs := steiner_normal_sections_law hT hy.
have ht : normal_scalar_section u T y t.
  by rewrite /normal_scalar_section /= /y /t normal_decomposition.
have hneT : normal_scalar_section u T y !=set0 by exists t.
have [s hsS] := (centered_section_support_law hs).2 hneT.
have hyr : inner_norm hB y<=r.
  exact (@normal_line_base_norm_bound R V B hB u hu y s r hy hr (hS _ hsS)).
pose a := Num.sqrt (r^+2-inner_norm hB y^+2).
have hA z : normal_scalar_section u S y z -> `|z|<=a.
  move=> hz; exact ((@normal_line_closed_ball_section R V B hB u hu y r z hy hr hyr).1 (hS _ hz)).
have htn := centered_section_norm_bound hs (sqrtr_ge0 _) hA ht.
have hnorm := (@normal_line_closed_ball_section R V B hB u hu y r t hy hr hyr).2 htn.
by rewrite /y /t normal_decomposition in hnorm.
Qed.
