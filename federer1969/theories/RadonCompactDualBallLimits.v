(** Federer (1969), 4.1.5, p. 350:
    the original unit weak-dual ball formula
    holds almost everywhere on the interior
    of each compact neighbourhood. The finite
    localization is derived from the Radon
    laws, not added to the original hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric MetricSubsetBackground GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousDualUP WeakEvaluationTopologyUP
  OpenFamilyTopologyMathcomp VectorDaniellHypotheses CompactContinuousVectorZeroExtension OpenSubspaceWeakDualExtension
  PartialFunctionBasic MeasureUP MeasureRestriction MeasurePushforward MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  RestrictedFunctionMeasurability RadonMeasureUP RadonBorelRegularity
  CompactFiniteMeasurePushforward FiniteEuclideanNormDerivationContext FiniteWeakDualBallQuotients
  SubtypeCompactHausdorff IsotropyGroupTopology SummableRealFunctionUP
  BallIntegralQuotientLimitUP OpenSubspaceLocalizedBallLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadonCompactDualBallLimits.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Variable U:set X.
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
Local Notation P := (fun x:UT=>forall y:Y,is_ball_integral_quotient_limit mu
  (real_total_integrand (fun z=>ed (xi z) y)) x (ed (xi x) y)).

(** Source for [radon_compact_dual_ball_limit_exception_null]:
    the simultaneous original ball formula has
    a null exceptional set in each compact
    interior, Federer 4.1.5, p. 350. *)
Theorem radon_compact_dual_ball_limit_exception_null (C:set T):
  compact C ->C `<=` U ->
  mu [set x:UT|interior C (set_val x) /\~P x]= 0%E.
Proof.
move=>hC hCU.
pose K:set UT:=(fun x:UT=>set_val x) @^-1` C.
have hK:compact K:=@set_type_compact_preimage T U C hC hCU.
have hKMeasurable:=@radon_compact_measurable R UT mu hm hr K hK.
have hKFinite:=@radon_compact_finite R UT mu hr K hK.
pose W:=@compact_vector_open_extension R T U D xi.
pose nu:=measure_pushforward (fun x:UT=>(set_val x:T)) (measure_restrict mu K).
have hInclusion:continuous (fun x:UT=>(set_val x:T)).
  exact:metric_subset_inclusion_continuous.
have[hNu [hNuRegular hNuFinite]]:=@compact_finite_continuous_pushforward R UT T mu hm
  (radon_borel_regular hm hr) K (fun x:UT=>(set_val x:T)) (@metric_hausdorff R T) hK hKFinite hInclusion.
have hRestricted:=measure_restrict_is_measure hm K.
have hXiRestricted:=measurable_function_for_restricted_measure hm K hXi.
have hWMeasurable:=@subspace_weak_dual_zero_extension_measurable R T U Y D ed xi O hO
  (measure_restrict mu K) hXiRestricted.
have hWUnit:=@subspace_unit_dual_zero_extension_bound R T U Y D ed xi NY hNY DN hD hUnit.
have hContext:=@finite_euclidean_norm_centered_derivation_context R n nu hNu hNuRegular hNuFinite.
have hAlmost:=@finite_weak_dual_simultaneous_ball_quotients R T Y NY hNY hSep D ed DN hD O hO
  nu W hContext hNuFinite hWMeasurable hWUnit.
apply:(@measure_null_subset R UT mu hm _
  (K `&` ((fun x:UT=>(set_val x:T)) @^-1`
    (~` [set a:T|forall y:Y,is_ball_integral_quotient_limit nu
      (real_total_integrand (fun z=>ed (W z) y)) a (ed (W a) y)]))) _ hAlmost).
move=>x [hInterior hNot]; split; first exact:interior_subset hInterior.
move=>hAt; apply:hNot=>y.
have hLocal:=@open_subspace_localized_ball_limit R T U C mu hm
  (fun z:UT=>ed (xi z) y) (fun z:T=>ed (W z) y) x (ed (xi x) y)
  hKMeasurable (fun z=>congr1 (fun a:D=>ed a y) (compact_vector_open_extension_value xi z)) hInterior.
apply:hLocal.
have hPoint:W (set_val x)=xi x:=compact_vector_open_extension_value xi x.
by rewrite -hPoint; exact:hAt y.
Qed.
End RadonCompactDualBallLimits.
