(** Federer (1969), 3.4.10, p. 338:
    the cited surface has original analytic dimension two.
    Reuse the checked polynomial upper bound and one
    genuine selected analytic sheet for the lower bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness AnalyticSetDimension AnalyticManifoldSubsetDimension
  AnalyticSubmanifoldUP BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed
  FunctionalAnalyticManifold BruhatWhitneySelectedSheet BruhatWhitneyPhysicalProjection
  BruhatWhitneyAuxiliaryEquation BruhatWhitneyAuxiliarySlice EuclideanBlockLinearMaps
  BruhatWhitneySurfaceAnalytic BruhatWhitneyDimensionUpper BruhatWhitneyAxis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_surface_dimension]: the
    actual surface in the example cited by 3.4.10,
    p. 338, has dimension two. Neither
    the local dimension nor the existence of a
    two-dimensional manifold is supplied as a premise. *)
Theorem bruhat_whitney_surface_dimension (R:realType):
  @analytic_set_dimension R 3 (@BruhatWhitneySurface.set R)= 2%N.
Proof.
have hOne:(1:R)!=0 by rewrite oner_eq0.
have [W [V [psi [hW [haW [hV [haV [hConvex [hPsi [hSolutions hUnique]]]]]]]]]]:=
  @bruhat_whitney_auxiliary_slice R 1 hOne.
pose Q:=@bruhat_whitney_physical_projection R.
pose U:set (R_n R 3):=[set v|V (Q v)].
pose j:=Ordinal (isT:(1<3)%N).
pose f:=@bruhat_whitney_selected_sheet_function R psi.
pose Z:set (R_n R 3):=[set v|U v /\v j=f v].
have [hFunctional hSubset]:=@bruhat_whitney_selected_sheet R V psi hPsi hSolutions.
have hZ:@is_euclidean_analytic_submanifold R 3 2 Z:=
  functional_analytic_submanifold_analytic hFunctional.
pose a:=@bruhat_whitney_axis R 1.
have ha:Z a.
  split.
  - change (V (Q a));rewrite /Q /a bruhat_whitney_axis_prefix;exact:haV.
  - change (a j=(a ord0)^+2*psi (Q a) ord_max).
    rewrite /a (bruhat_whitney_axis_coordinates (1:R)).1
      (bruhat_whitney_axis_coordinates (1:R)).2.1 expr0n mul0r;done.
have hAnalytic:=@bruhat_whitney_surface_locally_analytic R.
have hLower:=@analytic_manifold_subset_dimension R 3 2 (@BruhatWhitneySurface.set R) Z a
  (hAnalytic a Logic.I) hZ ha hSubset.
apply/eqP;rewrite eqn_leq;apply/andP;split.
- exact:bruhat_whitney_dimension_upper.
- exact:hLower.
Qed.
