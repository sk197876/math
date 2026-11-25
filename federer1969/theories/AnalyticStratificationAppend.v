(** Federer (1969), corrected 3.4.8(11), p. 327:
    combine the smaller-dimensional induction strata
    with the original final regular piece. The
    ordered append preserves the published disjointness
    and earlier-boundary requirements exactly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct FiniteDualDimension InnerNorm HilbertFormCompactness SetGermUP SetGermSealed
  FiniteAnalyticVarietyUP FunctionalAnalyticSubmanifoldUP GermVanishingSealed AnalyticDepthSealed
  SetGermLaws AnalyticFiniteStratificationUP InfiniteSequence OrdinalSetFamilySnoc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AppendStratum.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_stratification_append_regular]:
    append the original regular part after
    the smaller-dimensional strata in corrected
    3.4.8(11), pp. 327, 333–335.
    Every new-stratum requirement is retained;
    this theorem proves that the finite indexing
    preserves all earlier laws and the exact germ union. *)
Theorem analytic_stratification_append_regular
    (alpha gamma beta:@set_germ_space T 0) m (U0 S0:set X) mu
    (V S G:'I_mu->set X) (Vnew Snew Gnew:set X):
  @is_analytic_finite_stratification R n gamma beta m U0 S0 mu V S G ->
  @SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) =
    @SetGerms.join T 0 (@SetGerms.meet T 0 gamma (@SetGerms.neg T 0 beta)) (germ Snew) ->
  (@open T Vnew /\ Vnew 0 /\ Vnew `<=` U0) ->
  (exists d,(d<=m)%N /\ @is_functional_analytic_submanifold R n d Vnew Snew) ->
  finite_set (@connected_component T Snew @` Snew) ->
  (forall x,Snew x ->~(S0 `|` \bigcup_i S i) x) ->
  Vnew `&` @closure T Snew `<=` Snew `|` Gnew ->
  @is_finite_analytic_variety R X NX hNX Vnew Gnew ->
  (germ Gnew = germ set0 \/(depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ Gnew))<m)%N) ->
  Gnew `<=` S0 `|` \bigcup_i S i ->
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu.+1
    (ordinal_snoc V Vnew) (ordinal_snoc S Snew) (ordinal_snoc G Gnew).
Proof.
move=>hOld hSplit hNeighbourhood hFunctional hFinite hDisjoint hBoundary hAnalytic hDimension hEarlier.
constructor.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:analytic_stratification_neighbourhoods hOld j.
  + exact:hNeighbourhood.
- by rewrite ordinal_set_family_snoc_union hSplit (analytic_stratification_germ hOld)
    (@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)).
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:analytic_stratification_functional hOld j.
  + exact:hFunctional.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:analytic_stratification_components hOld j.
  + exact:hFinite.
- move=>i;case:(unliftP ord_max i)=>[j ->|->].
  + rewrite ordinal_snoc_lift ordinal_set_family_snoc_earlier.
    exact:analytic_stratification_disjoint hOld j.
  + rewrite ordinal_snoc_last ordinal_set_family_snoc_before_last.
    exact:hDisjoint.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:analytic_stratification_boundary hOld j.
  + exact:hBoundary.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:analytic_stratification_boundary_analytic hOld j.
  + exact:hAnalytic.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:analytic_stratification_boundary_dimension hOld j.
  + exact:hDimension.
- move=>i;case:(unliftP ord_max i)=>[j ->|->].
  + rewrite ordinal_snoc_lift ordinal_set_family_snoc_earlier.
    exact:analytic_stratification_boundary_earlier hOld j.
  + rewrite ordinal_snoc_last ordinal_set_family_snoc_before_last.
    exact:hEarlier.
Qed.
End AppendStratum.
