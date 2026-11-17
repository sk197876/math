(** Federer (1969), 3.4.8(13), pp. 328, 336:
    an original nonempty irreducible analytic germ has
    a compact, finite-Hausdorff-rectifiable representative with uniform
    diameter growth. Retain both dimension endpoints and the
    original norm topology used for analytic germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
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

(** Source for [analytic_irreducible_growth_representative]: the original
    representative conclusion of 3.4.8(13), p. 328,
    proved on p. 336. The finite nonnegative
    growth coefficient bounds every original subset by its
    diameter power, including zero-diameter subsets. *)
Theorem analytic_irreducible_growth_representative (R:realType) n
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0):
  @is_nonempty_irreducible_analytic_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha ->
  let m:=@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
    (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha) in
  exists (S:set (R_n R n)) (c:R),
    @compact (inner_metric_space (@euclidean_inner_productP R n)) S /\
    @set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S=alpha /\
    @is_measure_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m S /\
    @is_uniform_hausdorff_growth R (inner_metric_space (@euclidean_inner_productP R n)) m S c.
Proof.
move=>hIrreducible m.
pose X:=R_n R n;pose B:=@euclidean_inner_product R n;pose hB:=@euclidean_inner_productP R n.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose e:=@coordinate_basis R n;pose he:=@coordinate_basisP R n;pose omega:=dual_basis he.
pose I:=@AnalyticSetIdeal.value R X NX hNX 0 alpha.
have hAlpha:=hIrreducible.1.1;have hNonempty:=hIrreducible.2.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hBound:=(analytic_reduction_depth_bound (@AnalyticDepth.laws R X B hB n e he omega I)).
case:(posnP m)=>[hZero|hPositive].
- have hPoint:=@analytic_zero_depth_point_germ R X B hB n e he omega hDual alpha hAlpha hNonempty hZero.
  exists [set (0:X)],1;split;first exact:compact_set1.
  split;first exact:esym hPoint.
  have hEndpoints:=@singleton_zero_hausdorff_growth R n (0:X).
  by rewrite hZero.
- case:(ltnP m n)=>hMN.
  + pose mi:'I_n:=Ordinal hMN.
    have [U [H [hU0 [hH hHGerm]]]]:=hAlpha.
    have hIEquation:I=@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 H) by rewrite hHGerm.
    have hPrime:=(@analytic_irreducible_proper_prime_equivalence R X NX hNX 0 alpha hAlpha).1 hIrreducible.
    have hDepth:@AnalyticDepth.value R X B hB n e he omega I=(mi:nat):=erefl.
    have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=
      @analytic_prime_growth_representative R n I U H mi hU0 hH hIEquation hPrime hPositive hDepth.
    exists S,c;split;first exact:hCompact.
    split;first exact:eq_trans hGerm hHGerm.
    by split.
  + have hEqual:m=n by apply/eqP;rewrite eqn_leq hBound hMN.
    have hWhole:=@analytic_full_dimension_whole_germ R n alpha hAlpha hNonempty hEqual.
    have [S [c [hCompact [hGerm [hRect hGrowth]]]]]:=@euclidean_whole_growth_representative R n.
    exists S,c;split;first exact:hCompact.
    split;first exact:eq_trans hGerm (esym hWhole).
    by rewrite hEqual.
Qed.
