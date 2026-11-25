(** Federer (1969), 4.1.14, p. 371: continuous
    approximation weights are summable for a finite variation
    carried by the original compact support. This supporting
    form uses the integral comparison laws of 2.4.4–2.4.6,
    pp. 82–84. Uniform convergence is needed only on the
    carrying compact set, not on the whole open domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  PartialAbsolutePartsGraph PartialExtendedOrderLoci SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureStepIntegralIdentification MeasureIntegralGraphEquivalence
  MeasureAbsoluteSummability RadonMeasureUP FiniteMeasureBoundedNorm
  FiniteMeasureAlmostUniformIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactCarriedContinuousIntegral.
Variable R:realType.
Variable X:metricType R.
Variable mu:set X->\bar R.
Hypotheses (hm:is_measure mu) (hr:is_radon_measure mu).
Variable mass:R.
Hypothesis hMass:mu setT=mass%:E.
Variable K:set X.
Hypothesis hK:compact K.
Hypothesis hCarried:mu (~` K)=0.

(** Source for [compact_carried_continuous_integral_exists]:
    each continuous scalar approximation weight has an actual
    finite integral for the original finite compact-carried
    variation, supporting Federer 4.1.14, p. 371. *)
Theorem compact_carried_continuous_integral_exists (f:X->R^o):
  continuous f->exists a:R,
    is_measure_integral mu (real_total_integrand f) a%:E.
Proof.
move=>hF.
have hImage:compact (f @` K:set R^o).
  exact:continuous_compact (continuous_subspaceT hF) hK.
have[B hB]:=@filter_ex _ _ proper_pinfty_nbhs _ (compact_bounded hImage).
have hScalar:is_measure_measurable_function mu
    (partial_function_total (fun x=>(f x:real_line_metric R))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hm.
  - move=>O hO;rewrite partial_function_total_preimage.
    exact:(@radon_open_measurable R X mu hr (f @^-1` O)
      (((@continuousP X (real_line_metric R) f).1 hF) O hO)).
have hMeas:=@measurable_partial_real_embedding R X mu hm _ hScalar.
have hConstant:is_measure_integral mu (real_total_integrand (fun _:X=>B))
    (B*mass)%:E.
  have hRaw:=@finite_measure_constant_integral R X mu hm mass B hMass.
  apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hRaw)=>x y.
  exact:iff_sym (real_total_integrand_graph (fun _:X=>B) x y).
have hDom:measure_almost_everywhere mu
    (partial_extended_le_locus
      (partial_extended_function_absolute_value (real_total_integrand f))
      (real_total_integrand (fun _:X=>B))).
  apply:(@measure_almost_everywhere_mono R X mu hm K _ _ hCarried)=>x hx.
  exists (`|f x|)%:E,B%:E;split.
  - exists (f x)%:E;split;first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split;first by apply/real_total_integrand_graph.
    rewrite lee_fin;exact:hB (f x) (imageP f hx).
exact:(@measure_dominated_summable R X mu hm _ _ hMeas
  (ex_intro _ (B*mass) hConstant) hDom).1.
Qed.

(** Source for [compact_carried_continuous_integral_limit]:
    the original weighted scalar integral converges when its
    continuous weights converge uniformly on K, supporting
    Federer 4.1.14, p. 371. The asserted limit is any
    actual original integral witness, with no chosen-value premise. *)
Theorem compact_carried_continuous_integral_limit
    (f:nat->X->R^o) (g:X->R^o) (b:R):
  (forall i,continuous (f i))->
  is_measure_integral mu (real_total_integrand g) b%:E->
  (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,K x->`|f i x-g x|<eps)->
  exists a:nat->R,
    (forall i,is_measure_integral mu (real_total_integrand (f i)) (a i)%:E) /\
    forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|a i-b|<eps.
Proof.
move=>hF hG hUniform.
have hExists i:=compact_carried_continuous_integral_exists (hF i).
have[a hA]:=choice hExists.
exists a;split;first exact:hA.
apply:(@finite_measure_almost_uniform_integral_limit R X mu hm mass f g a b
  hMass hA hG)=>delta hDelta.
have[N hN]:=hUniform delta hDelta.
exists N=>i hi.
apply:(@measure_almost_everywhere_mono R X mu hm K _ _ hCarried)=>x hx.
exact:ltW (hN i hi x hx).
Qed.
End CompactCarriedContinuousIntegral.
