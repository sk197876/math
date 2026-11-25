(** Federer (1969), 4.1.14, p. 371: the original
    affine-chain mass is bounded by the literal variation
    integral of |g-f|sigma^m. Work on the internally
    derived open source W. The interval times T is flat
    on the exact compact cylinder; the unchanged original
    point specification gives the weak smooth-image limit.
    Finite mass supplies the source representation only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormScalarClassZeroTopology
  NormClassOneUP NormClassZeroTopology NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate LipschitzUP
  SmoothCompactSet CurrentDomain MetricSubsetBackground IsotropyGroupTopology
  CurrentSpaces CurrentMassSealed CurrentMassRepresentation CurrentFiniteMassRepresentation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentRadonSupport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentAffineHomotopySealed
  CurrentCompactTimeCylinder CurrentFlatTimeCylinder CurrentLipschitzCompactImage
  CurrentAffineMajorantApproximationUP CurrentSmoothApproximationUP FlatCurrentsUP
  FlatCurrentFinite CurrentCompactLipschitzPushforwardUP
  CurrentLipschitzImageOriginalApproximation CurrentCompactPushforwardAlgebra
  CurrentAffineMajorantSmoothImageMass CurrentAffineWeightMassLimit
  SummableRealFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineMajorantImageMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX U.
Variables f g:X->Y.
Variable sigma:X->R^o.
Variables (A:set R) (W:set X) (a b:nat->X->Y) (eta:nat->R).
Hypothesis hData:@is_current_affine_majorant_approximation R n nu U V K f g sigma
  A W a b eta.
Local Notation hA:=(current_affine_majorant_parameter hData).
Local Notation hW:=(current_affine_majorant_domain_open hData).
Local Notation hKW:=(current_affine_majorant_domain_contains hData).
Local Notation KW:=(@current_compact_index_in_open R n U W K hKW).
Local Notation WT:=(current_domain R n W).
Local Notation WM:=(metric_subset (W:set XT)).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A W).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT W hAT hW).
Local Notation KP:=(@current_compact_time_cylinder R n A W hA KW).
Local Notation H:=(@CurrentAffineHomotopy.value R n nu f g).
Local Notation Hi i:=(@CurrentAffineHomotopy.value R n nu (a i) (b i)).
Local Notation hHImage:=(current_affine_majorant_original_image hData).
Hypothesis hHLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNZ) YT AU H.
Hypotheses (hFClass:norm_class_zero NX NY W f)
  (hGClass:norm_class_zero NX NY W g)
  (hSigmaClass:norm_class_zero NX (fun t:R^o=>`|t|) W sigma).
Variable T:@current_space R h2 n W hW m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m W hW KW T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m W hW T< +oo)%E.
Local Notation time:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT W hAT hW time T).
Variable Q:@current_space R h2 nu V hV (1+m)%N.
Hypothesis hQ:@is_current_compact_lipschitz_image R h2 (1+n)%N nu (1+m)%N
  AU V hAU hV H hHImage hHLocal KP product Q.

(** Source for [current_affine_majorant_image_mass]: the original
    M(h#([0,1] times T)) <= ||T||(|g-f|sigma^m)
    on the derived source W, Federer 4.1.14, p. 371.
    T is any finite-mass flat current. Its representation
    is derived, and every source representation witness has
    the same literal original bound. No representation or
    normality of Q is assumed. *)
Theorem current_affine_majorant_image_mass:
  @is_integration_representable_current R h2 n m W hW T /\
  forall hT:@is_integration_representable_current R h2 n m W hW T,
    (@CurrentMass.value R h2 nu (1+m)%N V hV Q<=
      measure_lower_integral (@NormalisedCurrent.measure R h2 n m W hW T hT)
        (real_total_integrand (fun x:WT=>
          (NY (g (set_val x)-f (set_val x))*(sigma (set_val x))^+m)%R)))%E.
Proof.
split;first exact:(@current_finite_mass_representation R h2 n m W hW T hFinite).
move=>hT.
have hPFlat:=@flat_current_time_cylinder R h2 n m A W hA hW KW T hFlat.
pose hPCompact:=@flat_supported_current_compact R h2 (1+n)%N (1+m)%N AU hAU
  KP product hPFlat.
pose hHomApprox:=current_affine_majorant_homotopy_approximation hData.
pose images:=fun i=>@current_compact_map_pushforward R h2 (1+n)%N nu AU V hAU hV
  (Hi i) (current_smooth_approximation_image hHomApprox i)
  (current_smooth_approximation_class hHomApprox i) (1+m)%N product hPCompact.
have hWeak:=@current_lipschitz_image_original_approximation_weak R h2 (1+n)%N nu
  (1+m)%N AU V hAU hV H hHImage hHLocal KP product hPFlat Q hQ
  (fun i=>Hi i) hHomApprox.
pose mu:=@NormalisedCurrent.measure R h2 n m W hW T hT.
pose hBase:=normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m W hW T hT).
pose hm:=distribution_representation_measure hBase.
pose hr:=distribution_representation_radon hBase.
pose KT:set WM:=set_val @^-1` smooth_compact_carrier KW.
have hKT:compact KT:=@set_type_compact_preimage XT W
  (smooth_compact_carrier KW) (smooth_compact_is_compact KW) (smooth_compact_in_domain KW).
have hSupport:=@flat_current_supported_support R h2 n m W hW KW T hFlat.
have hCompact:=@flat_supported_current_compact R h2 n m W hW KW T hFlat.
have hCarried:mu (~` KT)=0.
  apply:(@measure_null_subset R WT mu hm _
    [set x:WT|~@current_support R h2 n W hW m T (set_val x)]).
  - move=>x hOff hS.
    have hKx:KT x:=@hSupport (set_val x) hS.
    exact (hOff hKx).
  - exact:(@current_radon_outside_support_null R h2 n m W hW T hT).
have hMassFinite:mu setT \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm setT)).
  by rewrite -(@current_represented_mass_total R h2 n m W hW T hT).
have hMass:mu setT=(fine (mu setT))%:E:=esym (fineK hMassFinite).
pose fw (x:WM):YT:=f (set_val x).
pose gw (x:WM):YT:=g (set_val x).
pose aw i (x:WM):YT:=a i (set_val x).
pose bw i (x:WM):YT:=b i (set_val x).
pose sw (x:WM):R^o:=sigma (set_val x).
have hFC:continuous fw:=@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY W f hFClass.
have hGC:continuous gw:=@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY W g hGClass.
have hSC:continuous sw:=@norm_class_zero_scalar_restriction_continuous
  R X NX hNX W sigma hSigmaClass.
pose hFirst:=current_affine_majorant_first_approximation hData.
pose hSecond:=current_affine_majorant_second_approximation hData.
have hAC:forall i,continuous (aw i).
  move=>i;exact:(@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY
    W (a i) (norm_class_continuous (current_smooth_approximation_class hFirst i 0%N))).
have hBC:forall i,continuous (bw i).
  move=>i;exact:(@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY
    W (b i) (norm_class_continuous (current_smooth_approximation_class hSecond i 0%N))).
have hError:forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|eta i|<eps.
  move=>eps hEps;have[N hN]:=current_affine_majorant_error_zero hData hEps.
  exists N=>i hi.
  rewrite (ger0_norm (ltW (current_affine_majorant_error_positive hData i))).
  exact:hN i hi.
apply:(@current_affine_weight_mass_limit R h2 nu (1+m)%N V hV images Q hWeak
  WM mu hm hr (fine (mu setT)) hMass KT hKT hCarried Y NY hNY
  fw gw aw bw sw eta m hFC hGC hSC hAC hBC _ _ hError).
- move=>eps hEps;have[N hN]:=current_smooth_approximation_uniform hFirst hEps.
  exists N=>i hi x hx;exact:hN i hi (set_val x) hx.
- move=>eps hEps;have[N hN]:=current_smooth_approximation_uniform hSecond hEps.
  exists N=>i hi x hx;exact:hN i hi (set_val x) hx.
- move=>i;exact:(@current_affine_majorant_smooth_image_mass R h2 n nu m
    U V hV K f g sigma A W a b eta hData T hT hSupport hCompact hPCompact i).
Qed.
End CurrentAffineMajorantImageMass.
