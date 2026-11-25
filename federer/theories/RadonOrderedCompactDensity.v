(** Federer (1969), 4.1.7, pp. 358–359:
    compact scalar integral domination gives
    a nonnegative density bounded by one.
    This supporting form reuses the original
    Radon consequence of 2.5.9, p. 100,
    and the all-set measure identification of
    the preceding exact-variation argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci RadonMeasureUP
  FunctionLatticeUP FunctionLatticeLaws CompactSupportFunctionUP CompactSupportFunctionLattice
  RealIntegralFunctionalUP RealIntegralFunctional MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum
  RealLatticeDensityUP RadonDominatedCompactDensity RadonBoundedPositiveDensity RadonBoundedDensityIdentification
  RadonCompactCoverCountablyMeasurable SummableRealFunctionUP LatticeL1ApproximationLaws
  MeasureIntegralUP MeasureIntegralComparison MeasureDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_ordered_compact_measure_density]:
    order of the actual positive compact
    integrals gives rho=k mu on every
    set with 0<=k<=1, supporting the
    Baire projection step of Federer 4.1.7,
    p. 359. The compact neighbourhood cover
    is supplied from the original open domain. *)
Theorem radon_ordered_compact_measure_density (R:realType) (X:metricType R)
    (mu rho:set X->\bar R) (hm:is_measure mu) (hn:is_measure rho)
    (hr:is_radon_measure mu) (hs:is_radon_measure rho)
    (F A:(X->R)->R) (C W:nat->set X):
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F->
  is_real_integral_functional rho (positive_function_lattice (@compactly_supported_continuous_functions R X)) A->
  (forall g,positive_function_lattice (@compactly_supported_continuous_functions R X) g->A g<=F g)->
  (forall j,compact (C j))->(forall j,open (W j))->(forall j,W j `<=` C j)->
  setT `<=` \bigcup_j C j->setT `<=` \bigcup_j W j->
  exists k:X->R,(forall x,0<=k x<=1) /\
    is_real_lattice_density mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) A k /\
    is_measure_density mu (real_total_integrand k) rho.
Proof.
move=>hF hA hOrder hC hW hWC hCover hWCover.
pose Kplus:=positive_function_lattice (@compactly_supported_continuous_functions R X).
have hL:=positive_function_lattice_laws (@compactly_supported_continuous_functions_lattice R X).
have hFM:=@real_integral_functional_is_monotone_daniell R X mu hm Kplus F hL hF.
have hAM:=@real_integral_functional_is_monotone_daniell R X rho hn Kplus A hL hA.
have hPositive g (hg:Kplus g):0<=A g.
  have hCompare:measure_almost_everywhere rho
      (partial_extended_le_locus (real_total_integrand (fun _=>0)) (real_total_integrand g)).
    apply:(@measure_almost_everywhere_mono R X rho hn setT _ _
      (measure_almost_everywhere_true hn))=>x _.
    exists (0:R)%:E,(g x)%:E;split;first by rewrite real_total_integrand_graph.
    split;first by rewrite real_total_integrand_graph.
    rewrite lee_fin;exact:hg.2 x.
  have h:=@measure_integral_monotone R X rho hn _ _ _ _
    (@real_total_zero_integral R X rho hn) (hA g hg) hCompare.
  by rewrite lee_fin in h.
have hBound g (hg:Kplus g):`|A g|<=F (fun x=>`|g x|).
  have hAbs:(fun x=>`|g x|)=g by apply:funext=>x;exact:ger0_norm (hg.2 x).
  rewrite hAbs (ger0_norm (hPositive g hg));exact:hOrder g hg.
have [k [hk hKBound]]:=@radon_dominated_compact_density R X mu hm hr F A hFM hF
  (monotone_daniell_integral_is_daniell hAM) hBound.
have hCount:=@radon_compact_cover_countably_measurable R X mu hm hr C hC hCover.
have [l [hl hRange]]:=@radon_bounded_positive_compact_density R X mu hm hr A k
  hCount hk hPositive hKBound.
have hDensity:=@radon_bounded_compact_density_identifies_measure R X mu rho hm hn hr hs A l C W
  hA hl hRange hC hW hWC hCover hWCover.
exists l;split;first exact:hRange.
split;[exact:hl|exact:hDensity].
Qed.
