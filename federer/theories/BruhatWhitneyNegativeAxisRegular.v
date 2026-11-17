(** Federer (1969), 3.4.10, p. 338:
    every negative z-axis point of the cited
    surface belongs to its original regular part.
    Reuse the actual analytic graph and open restriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric EuclideanCoordinateHalfspaces FunctionalAnalyticManifold
  AnalyticSubmanifoldOpenRestriction AnalyticRegularLocusUP AnalyticRegularLocusSealed
  AnalyticSetDimension BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed
  BruhatWhitneyPhysicalProjection BruhatWhitneyAuxiliarySlice BruhatWhitneySelectedSheet BruhatWhitneyNegativeGraph
  BruhatWhitneyAxis BruhatWhitneySurfaceDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_negative_axis_regular]: the
    negative half-axis is regular on the actual
    two-dimensional surface, supporting the cited counterexample
    of 3.4.10, p. 338. *)
Theorem bruhat_whitney_negative_axis_regular (R:realType) (b:R):
  b<0 ->@AnalyticRegularLocus.value R 3
    (@analytic_set_dimension R 3 (@BruhatWhitneySurface.set R))
    setT (@BruhatWhitneySurface.set R) (@bruhat_whitney_axis R b).
Proof.
move=>hb;rewrite bruhat_whitney_surface_dimension.
have hb0:b!=0 by rewrite (lt_eqF hb).
have [A [V [psi [hA [haA [hV [haV [hConvex [hPsi [hSolutions hUnique]]]]]]]]]]:=
  @bruhat_whitney_auxiliary_slice R b hb0.
pose X:=R_n R 3.
pose S:=@BruhatWhitneySurface.set R.
pose Q:=@bruhat_whitney_physical_projection R.
pose U:set X:=[set v|V (Q v)].
pose j:=Ordinal (isT:(1<3)%N).
pose f:=@bruhat_whitney_selected_sheet_function R psi.
pose Z:set X:=[set v|U v /\v j=f v].
pose W:=U `&` [set v:X|v ord_max<0].
have [hFunctional hSubset]:=@bruhat_whitney_selected_sheet R V psi hPsi hSolutions.
have hZ:=functional_analytic_submanifold_analytic hFunctional.
have hU:=hFunctional.2.1.
have hW:=openI hU (@euclidean_coordinate_lower_halfspace_open R 3 ord_max 0).
have hEqual:S `&` W=Z `&` W.
  apply:funext=>v;apply:propext;split.
  - move=>[hs [hu hz]];split;last by split.
    split;first exact:hu.
    exact:(@bruhat_whitney_negative_graph R V psi hSolutions v hu hz hs).
  - move=>[hv hw];split;[exact:hSubset v hv|exact:hw].
apply:(@AnalyticRegularLocus.laws R 3 2 setT S (@bruhat_whitney_axis R b)).2.
split;first exact:bruhat_whitney_axis_membership.
exists W;split;first exact:hW.
split.
- split.
  + change (V (Q (@bruhat_whitney_axis R b))).
    rewrite /Q bruhat_whitney_axis_prefix;exact:haV.
  + change (is_true (@bruhat_whitney_axis R b ord_max<0)).
    by rewrite (bruhat_whitney_axis_coordinates b).2.2.
split;first by move=>v _.
rewrite hEqual;exact:(@analytic_submanifold_open_restriction R 3 2 Z W hZ hW).
Qed.
