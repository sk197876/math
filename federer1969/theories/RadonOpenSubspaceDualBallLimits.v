(** Federer (1969), 4.1.5, p. 350:
    the original weak-dual density is recovered
    from its ball integrals almost everywhere
    on an arbitrary open U. The proved
    compact exhaustion assembles the finite
    localizations with a countable null union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP MetricSubsetBackground
  GrassmannAbbreviations FiniteCoordinates LinearBasis EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousDualUP WeakEvaluationTopologyUP OpenFamilyTopologyMathcomp VectorDaniellHypotheses
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP RadonMeasureUP
  SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactExhaustionSealed CompactExhaustionInteriorCover
  SummableRealFunctionUP BallIntegralQuotientLimitUP RadonCompactDualBallLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadonOpenSubspaceDualBallLimits.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Local Notation UT := (metric_subset (U:set T)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.
Variable O:set (set D).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable xi:UT->D.
Hypothesis hXi:is_measure_measurable_function mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))).
Hypothesis hUnit:forall x,DN (xi x)<= 1.

(** Source for [radon_open_subspace_dual_ball_limits]: the
    simultaneous original scalar ball formula
    on arbitrary open U, Federer 4.1.5,
    p. 350. Every original small radius
    has a positive finite denominator outside
    one null set, common to all y. *)
Theorem radon_open_subspace_dual_ball_limits:
  measure_almost_everywhere mu [set x:UT|forall y:Y,is_ball_integral_quotient_limit mu
    (real_total_integrand (fun z=>ed (xi z) y)) x (ed (xi x) y)].
Proof.
pose K:=@SmoothCompactExhaustion.value R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) U hU.
have hK:=@SmoothCompactExhaustion.laws R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) U hU.
pose P:=fun x:UT=>forall y:Y,is_ball_integral_quotient_limit mu
  (real_total_integrand (fun z=>ed (xi z) y)) x (ed (xi x) y).
pose Bad:=fun j=>[set x:UT|@interior T (smooth_compact_carrier (K j)) (set_val x) /\~P x].
have hBad j:mu (Bad j)= 0%E.
  exact:(@radon_compact_dual_ball_limit_exception_null R n U Y NY hNY hSep D ed DN hD O hO
    mu hm hr xi hXi hUnit (smooth_compact_carrier (K j))
    (smooth_compact_is_compact (K j)) (smooth_compact_in_domain (K j))).
have hUnion:=@measure_null_countable_union R UT [the choiceType of (nat:Type)] mu hm setT Bad
  (countableP setT) (fun j _=>hBad j).
apply:(@measure_null_subset R UT mu hm (~` P) (\bigcup_j Bad j) _ hUnion)=>x hNot.
have[j hInterior]:=@smooth_compact_exhaustion_interior_cover R X N hN U K hK (set_val x) (set_valP x).
exists j; first exact I; by split.
Qed.
End RadonOpenSubspaceDualBallLimits.
