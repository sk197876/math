(** Federer (1969), 4.1.14, p. 371: the
    original continuous affine weights have finite integrals
    against finite variation with compact support. Reuse
    the actual Radon support and total-mass laws of
    4.1.7, pp. 357–359, and 2.4.4–2.4.6, pp. 82–84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentMassSealed CurrentMassRepresentation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentRadonSupport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  IsotropyGroupTopology MetricSubsetBackground MeasureUP MeasureAlmostUP
  MeasureIntegralUP SummableRealFunctionUP CompactCarriedContinuousIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_compact_variation_continuous_integral]:
    a continuous original real weight has a finite
    integral for a finite-mass compact current, supporting
    Federer 4.1.14, p. 371. No normality or
    positivity of the weight is required. *)
Theorem current_compact_variation_continuous_integral
    (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E)
    (hCompact:@compact
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU m T))
    (F:current_domain R n U->R^o) (hF:continuous F) :
  exists c:R,is_measure_integral (@NormalisedCurrent.measure R h2 n m U hU T hT)
    (real_total_integrand F) c%:E.
Proof.
pose XT:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose UT:=current_domain R n U.
pose mu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
pose hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT).
pose hm:=distribution_representation_measure hBase.
pose hr:=distribution_representation_radon hBase.
pose K:set UT:=set_val @^-1` (@current_support R h2 n U hU m T).
have hK:compact K.
  exact:(@set_type_compact_preimage XT U (@current_support R h2 n U hU m T)
    hCompact (fun x hx=>hx.1)).
have hCarried:mu (~` K)=0.
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hMassFinite:mu setT \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm setT)).
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT).
have hMass:mu setT=(fine (mu setT))%:E:=esym (fineK hMassFinite).
exact:(@compact_carried_continuous_integral_exists R (metric_subset (U:set XT))
  mu hm hr (fine (mu setT)) hMass K hK hCarried F hF).
Qed.
