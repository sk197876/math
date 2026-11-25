(** Federer (1969), 3.4.8(11), pp. 333–334:
    apply the simultaneous smaller-depth induction to
    the original exceptional variety difference. The
    empty exceptional germ has no strata. All
    actual induction strata stay inside that variety. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermBoundary
  FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP
  AnalyticStratificationInductionUP AnalyticEmptyStratification AnalyticStratificationDimensionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ExceptionalInduction.
Variable R:realType.
Variable M:nat.
Hypothesis hInduction:forall d,(d<M)%N ->analytic_stratification_at_bound R d.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_exceptional_stratification_from_induction]:
    the smaller-dimensional var(K) minus beta
    in 3.4.8(11), pp. 333–334.
    Raise only the dimension bound; preserve the
    actual strata, neighbourhoods and corrected boundary laws. *)
Theorem analytic_exceptional_stratification_from_induction (U E U0 S0:set X):
  U 0 ->@is_finite_analytic_variety R X NX hNX U E ->
  U0 0 ->@is_finite_analytic_variety R X NX hNX U0 S0 ->
  (germ E = germ set0 \/(depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ E))<M)%N) ->
  exists mu,exists V S G:'I_mu->set X,
    @is_analytic_finite_stratification R n (germ E) (germ S0) M U0 S0 mu V S G /\
    forall i,S i `<=` E.
Proof.
move=>hU0 hE hU00 hS0 [hEmpty|hDrop].
- have hDifference:@SetGerms.meet T 0 (germ E) (@SetGerms.neg T 0 (germ S0)) = germ set0.
    rewrite hEmpty set_germ_intersection_commutative;exact:set_germ_intersection_empty.
  exists 0%N,(fun _=>set0),(fun _=>set0),(fun _=>set0);split.
  + exact:analytic_empty_stratification hDifference.
  + by move=>i;have:=ltn_ord i;rewrite ltn0.
- pose d:=depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ E)).
  have [mu [V [S [G [hLaws hInside]]]]]:=@hInduction d hDrop n U E U0 S0
    hU0 hE hU00 hS0 (leqnn d).
  exists mu,V,S,G;split;last exact:hInside.
  exact:analytic_stratification_dimension_bound hLaws (ltnW hDrop).
Qed.
End ExceptionalInduction.
