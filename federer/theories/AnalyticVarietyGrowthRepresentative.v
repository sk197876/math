(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), pp. 328, 336:
    an original nonempty irreducible analytic germ has
    a compact, finite-Hausdorff-rectifiable representative with uniform
    diameter growth. Retain both dimension endpoints and the
    original norm topology used for analytic germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import SetGermSealed AnalyticIrreducibleGrowthRepresentative UniformHausdorffGrowthUnions AnalyticIdealDepthMonotonicity AnalyticGermNoetherian NoetherianIrreducibleCover IrreducibleGermCoverUP SetGermFiniteUnion SetGermLaws MeasureRectifiableFiniteUnions CountablyMeasureRectifiableOperations HausdorffDimensionDrop MeasureAlmostBasic MeasureBasic MetricDiameter Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder AnalyticGermRing GermVanishingSealed AnalyticVarietyGermUP
  AnalyticIrreducibleGermUP AnalyticIrreducibleProperPrime CommutativeIdealUP
  AnalyticDepthSealed AnalyticReductionDepthUP AnalyticZeroDepthPointGerm AnalyticFullDimensionalCut AnalyticFullDimensionWholeGerm
  AnalyticPrimeGrowthRepresentative ElementaryHausdorffGrowthRepresentatives EuclideanWholeGrowthRepresentative
  HausdorffMeasure RectifiableSetUP UniformHausdorffGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


Section FiniteGrowth.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation E:=(inner_metric_space hB).
Local Notation germ:=(@set_germ T 0).
Local Notation G:=(@set_germ_space T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n) hB n
  (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_finite_irreducible_growth_representative]:
    finite-component assembly of the real-case growth estimate
    used in 3.4.12, p. 339. Lower-dimensional pieces
    have zero mass at the common degree; retain their compact
    sets, original germs and the actual all-subset estimate. *)
Theorem analytic_finite_irreducible_growth_representative (F:seq G) m:
  (forall beta,beta \in F ->@is_nonempty_irreducible_analytic_germ R X NX hNX 0 beta) ->
  (forall beta,beta \in F ->(depth (ideal beta)<=m)%N) ->
  exists (S:set X) (c:R),@compact E S /\germ S=@set_germ_finite_union T 0 F /\
    @is_measure_m_rectifiable R E (@hausdorff_measure R E m) m S /\
    @is_uniform_hausdorff_growth R E m S c.
Proof.
elim:F=>[|beta F ih] hMembers hBound.
- exists set0,0;split;first exact:compact0.
  split;first reflexivity.
  split;last exact:uniform_hausdorff_growth_empty.
  split;first exact:countably_measure_rectifiable_null (@hausdorff_measure_is_measure R E m)
    (measure_empty (@hausdorff_measure_is_measure R E m)).
  by rewrite (measure_empty (@hausdorff_measure_is_measure R E m)) lt0y.
- have hBeta:=hMembers beta (mem_head beta F).
  have hBetaBound:=hBound beta (mem_head beta F).
  have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=
    @analytic_irreducible_growth_representative R n beta hBeta.
  have hSM:exists d:R,@is_measure_m_rectifiable R E (@hausdorff_measure R E m) m S /\
      @is_uniform_hausdorff_growth R E m S d.
    case:(eqVneq (depth (ideal beta)) m)=>hEqual.
    + exists c;by rewrite -hEqual.
    + have hStrict:(depth (ideal beta)<m)%N by rewrite ltn_neqAle hEqual hBetaBound.
      have hNull:=@hausdorff_finite_mass_higher_degree_zero R E
        (depth (ideal beta)) m S hStrict hRect.2.
      exists 0;split.
      * split;first exact:countably_measure_rectifiable_null (@hausdorff_measure_is_measure R E m) hNull.
        by rewrite hNull lt0y.
      * exact:uniform_hausdorff_growth_higher_degree hStrict hRect.2 hGrowth.
  have [d [hRectM hGrowthM]]:=hSM.
  have hTailMembers gamma (hGamma:gamma \in F):@is_nonempty_irreducible_analytic_germ R X NX hNX 0 gamma.
    apply:hMembers;by rewrite in_cons hGamma orbT.
  have hTailBound gamma (hGamma:gamma \in F):(depth (ideal gamma)<=m)%N.
    apply:hBound;by rewrite in_cons hGamma orbT.
  have [A [a [hACompact [hAGerm [hARect hAGrowth]]]]]:=ih hTailMembers hTailBound.
  exists (S `|` A),(d+a);split;first exact:compactU hCompact hACompact.
  split.
  + rewrite -(@set_germ_union_equation T 0 _ _ _ (@SetGerms.laws T 0)) hGerm hAGerm;reflexivity.
  split;last exact:uniform_hausdorff_growth_union hGrowthM hAGrowth.
  have hFamily:forall j:bool,@is_measure_m_rectifiable R E (@hausdorff_measure R E m) m
      (if j then S else A) by case.
  have hUnion:(\bigcup_j (if j:bool then S else A))=S `|` A.
    apply/seteqP;split.
    * by move=>x [[] _ hx];[left|right].
    * move=>x [hx|hx];[by exists true|by exists false].
  rewrite -hUnion;exact:measure_rectifiable_finite_union (@hausdorff_measure_is_measure R E m) hFamily.
Qed.

(** Source for [analytic_variety_growth_representative_at_bound]: the
    real-case representative estimate used in 3.4.12, p. 339,
    for any actual analytic variety germ, including a reducible
    or empty germ. Reuse its proved finite irreducible decomposition
    and the original ideal-depth monotonicity. *)
Theorem analytic_variety_growth_representative_at_bound (alpha:G) m:
  @is_analytic_variety_germ R X NX hNX 0 alpha ->(depth (ideal alpha)<=m)%N ->
  exists (S:set X) (c:R),@compact E S /\germ S=alpha /\
    @is_measure_m_rectifiable R E (@hausdorff_measure R E m) m S /\
    @is_uniform_hausdorff_growth R E m S c.
Proof.
move=>hAlpha hBound.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R X NX hNX n (@coordinate_basis R n)
  0 (@coordinate_basisP R n).
have [F hCover]:=@noetherian_finite_irreducible_germ_cover R X NX hNX 0 hNoetherian alpha hAlpha.
have hUnion:=irreducible_germ_cover_union hCover.
have hMembers:=irreducible_germ_cover_members hCover.
have hEach beta (hBeta:beta \in F):(depth (ideal beta)<=m)%N.
  apply:leq_trans _ hBound.
  apply:(@analytic_variety_ideal_depth_monotone R X (@euclidean_inner_product R n) hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n)) beta alpha).
  rewrite -hUnion;exact:set_germ_finite_union_member hBeta.
have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=
  analytic_finite_irreducible_growth_representative hMembers hEach.
exists S,c;split=>//;by rewrite -hUnion.
Qed.
End FiniteGrowth.
