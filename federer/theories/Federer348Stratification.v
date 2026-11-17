(** Federer (1969), 3.4.8(11), p. 327,
    proved on pp. 333–335: the complete original
    finite analytic stratification. Apply the published
    correction at p. 327 line 24 in full.
    The underlying depth is the original dimension;
    all existence and component bounds are proved by
    the simultaneous induction within this project. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP AnalyticVarietyGermUP
  FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP
  AnalyticFiniteStratificationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_8_11]:
    every assertion of corrected 3.4.8(11), p. 327:
    exact difference germ, finite actual components,
    functional analytic strata of dimension at most m,
    disjointness from earlier strata, and smaller analytic
    boundaries contained in those earlier strata.
    Empty boundary germs are explicit because the book
    defines dimension only for nonempty variety germs. *)
Theorem federer_3_4_8_11 (R:realType) n
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    m (U0 S0:set (R_n R n)):
  @is_analytic_variety_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 set0 ->
  @AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha) = m ->
  U0 0 ->@is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U0 S0 ->
  @set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S0 = beta ->
  exists mu,exists V S G:'I_mu->set (R_n R n),
    @is_analytic_finite_stratification R n alpha beta m U0 S0 mu V S G.
Proof.
move=>[U [H [hU0 [hH hAlpha]]]] hNonempty hDepth hU00 hS0 hBeta.
have hBound:=hDepth;rewrite -hAlpha in hBound.
have hAtBound:(@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
    (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (0%R:R_n R n)
      (@set_germ (Topological.clone (real_norm_metric_space
        (inner_norm_real_norm (@euclidean_inner_productP R n))) _) (0%R:R_n R n) H))<=m)%N.
  by rewrite hBound.
have [mu [V [S [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R m
  n U H U0 S0 hU0 hH hU00 hS0 hAtBound.
rewrite hAlpha hBeta in hLaws.
exists mu,V,S,G;exact:hLaws.
Qed.
