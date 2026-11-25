(** Federer (1969), 4.1.14, p. 371: the actual
    variation integrals of h(g_i)(sigma+eta_i)^m converge
    to the original integral of h(f)sigma^m. The source
    current need only have finite mass and support in K;
    normality and a derivative bound for its variation
    measure are not required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormDifferentialUP NormScalarClassZeroTopology
  NormClassOneUP NormClassZeroTopology NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentMassSealed CurrentMassRepresentation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentRadonSupport
  CurrentProperSupportDomain SmoothCompactSet MetricSubsetBackground
  MetricProductBackground IsotropyGroupTopology CompactWeightedImageUniform
  CompactCarriedContinuousIntegral DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP FunctionLatticeUP CompactSupportFunctionUP
  PartialFunctionBasic SummableRealFunctionUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic RadonMeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentWeightedApproximationIntegralLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation VT:=(current_domain R nu V).
Local Notation UM:=(metric_subset (U:set XT)).
Local Notation VM:=(metric_subset (V:set YT)).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E.
Variable K:smooth_compact_set hNX U.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` smooth_compact_carrier K.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Let hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT).
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_zero NX NY U f.
Variable sigma:X->R^o.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Variable g:nat->X->Y.
Hypothesis hImages:forall i x,U x->V (g i x).
Hypothesis hSmooth:forall i,norm_class_all_orders hNX hNY U (g i).
Hypothesis hUniform:forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
  forall x,smooth_compact_carrier K x->NY (g i x-f x)<eps.
Variable eta:nat->R.
Hypothesis hError:forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|eta i|<eps.
Local Notation fU:=(@current_map_on_domain R n nu U V f hImage).
Local Notation giU i:=(@current_map_on_domain R n nu U V (g i) (hImages i)).

(** Source for [current_weighted_approximation_integral_limit]:
    the precise scalar limit needed for the weighted variation
    inequality of Federer 4.1.14, p. 371. Every original
    positive compact target scalar test is allowed, including
    in degree zero and on an empty original domain. *)
Theorem current_weighted_approximation_integral_limit
    (h:VT->R) (b:R):
  positive_function_lattice (@compactly_supported_continuous_functions R VT) h->
  is_measure_integral mu
    (real_total_integrand (fun x=>h (fU x)*(sigma (set_val x))^+m)) b%:E->
  exists a:nat->R,
    (forall i,is_measure_integral mu
      (real_total_integrand (fun x=>h (giU i x)*
        (sigma (set_val x)+eta i)^+m)) (a i)%:E) /\
    forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|a i-b|<eps.
Proof.
move=>hH hIntegral.
pose KT:set UT:=set_val @^-1` smooth_compact_carrier K.
have hKT:compact KT:=@set_type_compact_preimage XT U
  (smooth_compact_carrier K) (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
have hCarried:mu (~` KT)=0.
  apply:(@measure_null_subset R UT mu hm _
    [set x:UT|~@current_support R h2 n U hU m T (set_val x)]).
  - move=>x hOff hS.
    have hKx:KT x:=@hSupport (set_val x) hS.
    exact (hOff hKx).
  - exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hMassFinite:mu setT \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm setT)).
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT).
have hMass:mu setT=(fine (mu setT))%:E:=esym (fineK hMassFinite).
have hFContinuous:=@current_map_on_domain_continuous R n nu U V f hImage hf.
pose s (x:UT):R^o:=sigma (set_val x).
have hSContinuous:continuous s.
  exact:(@norm_class_zero_scalar_restriction_continuous R X NX hNX U sigma hSigma).
pose pair (x:UT):metric_product VM (real_line_metric R):=(fU x,s x).
have hPairContinuous:continuous pair.
  move=>x;exact:cvg_pair (@hFContinuous x) (@hSContinuous x).
have hImageCompact:compact (pair @` KT).
  exact:continuous_compact (continuous_subspaceT hPairContinuous) hKT.
have hMapUniform:forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,KT x->mdist (giU i x:VM) (fU x:VM)<eps.
  move=>eps hEps;have[N hN]:=@hUniform eps hEps.
  exists N=>i hi x hx.
  change (is_true (NY (g i (set_val x)-f (set_val x))<eps)).
  exact:hN i hi (set_val x) hx.
have hWeightsUniform:=@compact_weighted_image_uniform R UT VM KT fU
  (fun i=>giU i) s eta h m hImageCompact hH.1.1 hMapUniform hError.
have hWeightContinuous:forall i,continuous
    (fun x:UT=>(h (giU i x)*(s x+eta i)^+m:R^o)).
  move=>i.
  have hGi:=@current_map_on_domain_continuous R n nu U V (g i) (hImages i)
    (norm_class_continuous (hSmooth i 0%N)).
  have hScalar:continuous (fun x:UT=>(s x+eta i:R^o)).
    have hConstant:continuous (fun _:UT=>(eta i:R^o)).
      move=>x.
      exact:(@cvg_cst [the topologicalType of R^o] (eta i) UT
        (nbhs x) (@nbhs_filter UT x)).
    move=>x.
    exact:(@cvgD R _ UT (nbhs x) (@nbhs_filter UT x)
      s (fun _:UT=>eta i) (s x) (eta i) (@hSContinuous x) (@hConstant x)).
  have hPower:forall k:nat,continuous (fun x:UT=>((s x+eta i)^+k:R^o)).
    elim=>[|k ih] x.
    - exact:(@cvg_cst [the topologicalType of R^o] 1 UT
        (nbhs x) (@nbhs_filter UT x)).
    - have hExp:(fun y:UT=>(s y+eta i)^+k.+1)=
        (fun y:UT=>(s y+eta i)*(s y+eta i)^+k).
        by apply:funext=>y;rewrite exprS.
      rewrite hExp.
      exact:(@cvgM R UT (nbhs x) (@nbhs_filter UT x)
        (fun y:UT=>s y+eta i) (fun y:UT=>(s y+eta i)^+k)
        (s x+eta i) ((s x+eta i)^+k) (@hScalar x) (@ih x)).
  move=>x.
  exact:(@cvgM R UT (nbhs x) (@nbhs_filter UT x)
    (fun y:UT=>h (giU i y)) (fun y:UT=>(s y+eta i)^+m)
    (h (giU i x)) ((s x+eta i)^+m)
    (@continuous_comp UT VT (real_line_metric R) (fun y=>giU i y)
      h x (@hGi x) (hH.1.1 (giU i x))) (@hPower m x)).
exact:(@compact_carried_continuous_integral_limit R UM mu hm hr
  (fine (mu setT)) hMass KT hKT hCarried
  (fun i x=>h (giU i x)*(s x+eta i)^+m)
  (fun x=>h (fU x)*(s x)^+m) b hWeightContinuous hIntegral hWeightsUniform).
Qed.
End CurrentWeightedApproximationIntegralLimit.
