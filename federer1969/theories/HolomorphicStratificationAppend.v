(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327:
    combine the smaller-dimensional induction strata
    with the original final regular piece. The
    ordered append preserves the published disjointness
    and earlier-boundary requirements exactly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct FiniteDualDimension InnerNorm HilbertFormCompactness SetGermUP SetGermSealed
  FiniteHolomorphicVarietyUP FunctionalHolomorphicSubmanifoldUP HolomorphicGermVanishingSealed HolomorphicDepthSealed
  SetGermLaws HolomorphicFiniteStratificationUP InfiniteSequence OrdinalSetFamilySnoc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AppendStratum.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@HolomorphicDepth.value R X (@standard_hermitian_product R n)
  (@standard_hermitian_productP R n) n (@coordinate_basis (ComplexScalars.C R) n) (@coordinate_basisP (ComplexScalars.C R) n)
  (dual_basis (@coordinate_basisP (ComplexScalars.C R) n))).

(** Source for [holomorphic_stratification_append_regular]:
    append the original regular part after
    the smaller-dimensional strata in corrected
    3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333–335.
    Every new-stratum requirement is retained;
    this theorem proves that the finite indexing
    preserves all earlier laws and the exact germ union. *)
Theorem holomorphic_stratification_append_regular
    (alpha gamma beta:@set_germ_space T 0) m (U0 S0:set X) mu
    (V S G:'I_mu->set X) (Vnew Snew Gnew:set X):
  @is_holomorphic_finite_stratification R n gamma beta m U0 S0 mu V S G ->
  @SetGerms.meet T 0 alpha (@SetGerms.neg T 0 beta) =
    @SetGerms.join T 0 (@SetGerms.meet T 0 gamma (@SetGerms.neg T 0 beta)) (germ Snew) ->
  (@open T Vnew /\ Vnew 0 /\ Vnew `<=` U0) ->
  (exists d,(d<=m)%N /\ @is_functional_holomorphic_submanifold R n d Vnew Snew) ->
  finite_set (@connected_component T Snew @` Snew) ->
  (forall x,Snew x ->~(S0 `|` \bigcup_i S i) x) ->
  Vnew `&` @closure T Snew `<=` Snew `|` Gnew ->
  @is_finite_holomorphic_variety R X NX hNX Vnew Gnew ->
  (germ Gnew = germ set0 \/(depth (@HolomorphicSetIdeal.value R X NX hNX 0 (germ Gnew))<m)%N) ->
  Gnew `<=` S0 `|` \bigcup_i S i ->
  @is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu.+1
    (ordinal_snoc V Vnew) (ordinal_snoc S Snew) (ordinal_snoc G Gnew).
Proof.
move=>hOld hSplit hNeighbourhood hFunctional hFinite hDisjoint hBoundary hHolomorphic hDimension hEarlier.
constructor.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:holomorphic_stratification_neighbourhoods hOld j.
  + exact:hNeighbourhood.
- by rewrite ordinal_set_family_snoc_union hSplit (holomorphic_stratification_germ hOld)
    (@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)).
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:holomorphic_stratification_functional hOld j.
  + exact:hFunctional.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:holomorphic_stratification_components hOld j.
  + exact:hFinite.
- move=>i;case:(unliftP ord_max i)=>[j ->|->].
  + rewrite ordinal_snoc_lift ordinal_set_family_snoc_earlier.
    exact:holomorphic_stratification_disjoint hOld j.
  + rewrite ordinal_snoc_last ordinal_set_family_snoc_before_last.
    exact:hDisjoint.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:holomorphic_stratification_boundary hOld j.
  + exact:hBoundary.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:holomorphic_stratification_boundary_holomorphic hOld j.
  + exact:hHolomorphic.
- move=>i;case:(unliftP ord_max i)=>[j ->|->];rewrite ?ordinal_snoc_lift ?ordinal_snoc_last.
  + exact:holomorphic_stratification_boundary_dimension hOld j.
  + exact:hDimension.
- move=>i;case:(unliftP ord_max i)=>[j ->|->].
  + rewrite ordinal_snoc_lift ordinal_set_family_snoc_earlier.
    exact:holomorphic_stratification_boundary_earlier hOld j.
  + rewrite ordinal_snoc_last ordinal_set_family_snoc_before_last.
    exact:hEarlier.
Qed.
End AppendStratum.
