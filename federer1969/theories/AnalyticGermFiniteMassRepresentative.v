(** Federer (1969), 3.4.10, p. 337:
    a variety germ of dimension at most k
    has a compact representative of finite H^k mass.
    Use the original irreducible decomposition and the
    compact representatives already proved in 3.4.8(13).
    No new rectifiability or measure theorem is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermFiniteUnion
  AnalyticGermRing GermVanishingSealed AnalyticDepthSealed
  AnalyticVarietyGermUP AnalyticIrreducibleGermUP AnalyticGermNoetherian
  IrreducibleGermCoverUP NoetherianIrreducibleCover AnalyticIdealDepthMonotonicity
  AnalyticIrreducibleGrowthRepresentative RectifiableSetUP HausdorffMeasure
  HausdorffDimensionDrop MeasureUP MeasureBasic MeasureFiniteUnionMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteMassRepresentative.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation E:=(inner_metric_space hB).
Local Notation G:=(@set_germ_space T 0).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  hB n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_germ_finite_mass_representative]: the
    local finite-mass input to 3.4.10, p. 337.
    It retains arbitrary natural degree above the actual
    germ dimension, arbitrary reducible germs and the
    empty germ. The compact representative is an existence
    witness; its construction is not a public definition. *)
Theorem analytic_germ_finite_mass_representative (alpha:G) k:
  @is_analytic_variety_germ R X NX hNX 0 alpha ->
  (depth (ideal alpha)<=k)%N ->
  exists S:set X,@compact E S /\germ S=alpha /\
    (@hausdorff_measure R E k S< +oo)%E.
Proof.
move=>hAlpha hBound.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R X NX hNX n
  (@coordinate_basis R n) 0 (@coordinate_basisP R n).
have [F hCover]:=@noetherian_finite_irreducible_germ_cover R X NX hNX 0
  hNoetherian alpha hAlpha.
have hMembers:=irreducible_germ_cover_members hCover.
have hUnion:=irreducible_germ_cover_union hCover.
have hComponents beta (hBeta:beta \in F):(depth (ideal beta)<=k)%N.
  apply:(leq_trans _ hBound).
  apply:(@analytic_variety_ideal_depth_monotone R X (@euclidean_inner_product R n)
    hB n (@coordinate_basis R n) (@coordinate_basisP R n)
    (dual_basis (@coordinate_basisP R n)) beta alpha).
  rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
have hFiniteUnion:forall L:seq G,
    (forall beta,beta \in L ->@is_nonempty_irreducible_analytic_germ R X NX hNX 0 beta) ->
    (forall beta,beta \in L ->(depth (ideal beta)<=k)%N) ->
    exists S:set X,@compact E S /\germ S=@set_germ_finite_union T 0 L /\
      (@hausdorff_measure R E k S< +oo)%E.
  elim=>[|beta L ih] hIrreducible hDimensions.
  - exists set0;split;first exact:compact0.
    split;first reflexivity.
    by rewrite (measure_empty (@hausdorff_measure_is_measure R E k)) lt0y.
  - have hBeta:beta \in beta::L by rewrite in_cons eqxx.
    have [A [c [hACompact [hAGerm [hARect hGrowth]]]]]:=
      @analytic_irreducible_growth_representative R n beta (hIrreducible beta hBeta).
    have hAFinite:(@hausdorff_measure R E k A< +oo)%E.
      have hD:=hDimensions beta hBeta.
      case:(eqVneq (depth (ideal beta)) k)=>hEqual.
      + rewrite -hEqual;exact:hARect.2.
      + have hLess:(depth (ideal beta)<k)%N by rewrite ltn_neqAle hEqual hD.
        have hZero:=@hausdorff_finite_mass_higher_degree_zero R E
          (depth (ideal beta)) k A hLess hARect.2.
        by rewrite hZero lt0y.
    have hTail beta' (hBeta':beta' \in L):beta' \in beta::L by rewrite in_cons hBeta' orbT.
    have [B [hBCompact [hBGerm hBFinite]]]:=ih
      (fun gamma hGamma=>hIrreducible gamma (hTail gamma hGamma))
      (fun gamma hGamma=>hDimensions gamma (hTail gamma hGamma)).
    exists (A `|` B);split;first exact:compactU hACompact hBCompact.
    split.
    + rewrite -(@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0) A B) hAGerm hBGerm.
      reflexivity.
    + exact:(measure_binary_union_finite_mass (@hausdorff_measure_is_measure R E k) hAFinite hBFinite).
have [S [hCompact [hGerm hMass]]]:=hFiniteUnion F hMembers hComponents.
exists S;split;first exact:hCompact.
split;[exact:eq_trans hGerm hUnion|exact:hMass].
Qed.
End FiniteMassRepresentative.
