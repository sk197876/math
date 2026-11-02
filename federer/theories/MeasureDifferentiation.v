(** Federer (1969), 2.9.8, p. 156: a locally absolutely integrable
    extended-real measurable function is the Vitali limit of its integral
    means almost everywhere. The proof applies the nonnegative theorem to
    both parts, proves finite values almost everywhere from local absolute
    integrability, and subtracts their finite means on a fine common domain.
    its class uses a countable finite open cover, whereas the theorem below
    retains Federer's bounded-set hypotheses. The scalar range in both PDFs
    is the extended real line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableExtendedParts
  MeasureDerivationContext CoveringRelationUP CoveringRelationLimits VitaliNullFibers
  MeasureMeanFunction LocalAbsoluteIntegrability LocalAbsoluteFiniteValues
  PartialFunctionIntegralParts MeasureUpperIntegralPositivePart MeasureIntegralPartsExist
  NonnegativeMeasureDifferentiation SignedMeanLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_9_8]: direct complete theorem
    Federer 2.9.8, p. 156. The extended-real
    measurable function has finite absolute integrals
    on all bounded measurable targets; its actual
    partial integral means converge to it almost
    everywhere. Zero denominators and undefined integrals
    are excluded by graph domains, and no extra
    pointwise-finiteness hypothesis is imposed. *)
Theorem federer_2_9_8 (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (extended_real_line R)) :
  is_measure_derivation_context phi V -> is_measure_measurable_function phi f ->
  is_locally_absolutely_integrable phi f ->
  measure_almost_equal phi (covering_relation_limit V (measure_mean_function phi f)) f.
Proof.
move=> hc hf hlocal.
have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hfp := @measurable_extended_positive_part R X phi hm f hf.
have hfn := @measurable_extended_negative_part R X phi hm f hf.
have [hpos hneg] := @partial_parts_nonnegative_almost R X phi hm f (measurable_function_domain hf).
have [hPlocal hNlocal] := @locally_absolutely_integrable_parts R X phi f hm hf hlocal.
have hPmean := @nonnegative_measure_differentiation R X phi V (partial_extended_function_positive_part f)
  hc hfp hpos hPlocal.
have hNmean := @nonnegative_measure_differentiation R X phi V (partial_extended_function_negative_part f)
  hc hfn hneg hNlocal.
have hfinite := @locally_absolutely_integrable_finite_almost R X phi f hphi hf hlocal.
pose P := [set x | covering_relation_fine_at (fun x S => V x S /\ phi S=0) x].
have hPzero : phi P=0 := @vitali_null_fine_points_null R X phi V hm (derivation_context_vitali hc).
have hnotP : measure_almost_everywhere phi (~` P) by rewrite /measure_almost_everywhere setCK.
have hmeans := @measure_almost_everywhere_and R X phi hm _ _ hPmean hNmean.
have hgood := @measure_almost_everywhere_and R X phi hm _ _ hfinite hnotP.
have hall := @measure_almost_everywhere_and R X phi hm _ _ hmeans hgood.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hall)=> x
  [[[vp [hLp hPgraph]] [vn [hLn hNgraph]]] [[y [hy hyfin]] hnP]].
pose c := fine y.
have hey : y=c%:E by rewrite /c fineK.
pose p := (Num.max c 0)%R.
pose n := (Num.max (-c) 0)%R.
have ep : vp=p%:E.
  have [a [ha hav]] := hPgraph.
  have eay := partial_function_single_valued ha hy.
  rewrite eay hey /extended_positive_part -EFin_max in hav; exact: esym hav.
have en : vn=n%:E.
  have [a [ha hav]] := hNgraph.
  have eay := partial_function_single_valued ha hy.
  rewrite eay hey /extended_negative_part /extended_positive_part -EFinN -EFin_max in hav; exact: esym hav.
rewrite ep in hLp; rewrite en in hLn.
have hdiff : (p-n=c)%R.
  change ((Num.max c 0-Num.max (-c) 0=c)%R).
  case: (leP 0%R c)=> hsign.
  - have hnc : (-c<=0)%R by rewrite oppr_le0.
    by rewrite (max_r hnc) subr0.
  - have hc0 : (c<=0)%R := ltW hsign.
    have hnc : (0<=-c)%R by rewrite oppr_ge0.
    by rewrite (max_l hnc) sub0r opprK.
have hsigned := @signed_mean_limit_from_parts R X phi V f x p n hc hf hlocal hnP hLp hLn.
rewrite hdiff in hsigned.
exists c%:E; split; [exact hsigned|by rewrite -hey].
Qed.
