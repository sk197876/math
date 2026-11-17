(** Federer (1969), 3.4.8(11), p. 333:
    smaller-depth stratifications supply the actual local
    component bounds for the critical variety, simultaneously
    in every finite ambient dimension. The strata
    lie inside the original analytic representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP FiniteAnalyticVarietyUP
  FiniteAnalyticVarietyBoundary GermVanishingSealed AnalyticDepthSealed AnalyticFiniteStratificationUP
  AnalyticStratificationInductionUP AnalyticStratificationLocalFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LowerLocal.
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

(** Source for [analytic_stratification_lower_local_components]:
    the original smaller-dimension induction implies
    local finiteness of H's actual components,
    3.4.8(11), p. 333. No compactness
    or component finiteness of H is an input. *)
Theorem analytic_stratification_lower_local_components (U H:set X):
  U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
  (depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ H))<M)%N ->
  exists O:set X,@open T O /\O 0 /\
    finite_set (@connected_component T H @` (H `&` O)).
Proof.
move=>hU0 hH hDepth.
pose d:=depth (@AnalyticSetIdeal.value R X NX hNX 0 (germ H)).
have hEmpty:@is_finite_analytic_variety R X NX hNX U set0:=finite_analytic_variety_domain_empty hH.1.
have [mu [V [S [G [hLaws hInside]]]]]:=@hInduction d hDepth n U H U set0
  hU0 hH hU0 hEmpty (leqnn d).
exact:analytic_stratification_local_component_finiteness hLaws hInside.
Qed.
End LowerLocal.
