(** Federer (1969), 4.1.18, p. 375: the
    actual variation measures of T_epsilon converge
    weakly to the original variation of every
    representable T. Compact positive tests suffice
    for the original Daniell weak topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  FiniteNormEquivalence AlternatingForms CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationUP DistributionVariationParameterSqueeze
  FunctionLatticeUP FunctionLatticeLaws CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactCutoffUP CompactCutoffSealed MonotoneDaniellIntegralLaws
  CompactDaniellFixedSupportUniform RadonCompactScalarIntegral
  SmoothingKernelUP SmoothingDilationUP CurrentSmoothingOperators
  CurrentSmoothingOriginalGaugeUpper CurrentSmoothingRepresentable CurrentAmbientVariation
  PositiveCompactSmoothingFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingWeakVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation values:=(smooth_test_values_hom hE).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation action:=(@current_value R h2 n Full hFull m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable T:C.
Hypothesis hT:@is_integration_representable_current R h2 n m Full hFull T.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily T).
Local Notation hSmooth:=(@current_smoothing_representable R h2 n m phi family hPhi hFamily T).
Local Notation mu:=(@current_ambient_variation R h2 n m T hT).
Local Notation hm:=(@current_ambient_variation_laws R h2 n m T hT).1.
Local Notation hr:=(@current_ambient_variation_laws R h2 n m T hT).2.
Local Notation D:=(@radon_positive_compact_integral R XT mu hm hr).

(** Source for [current_smoothing_ambient_variation_integral]:
    the actual original compact positive integral
    ||T_epsilon||(f), used in 4.1.18, p. 375.
    Representability is proved internally from the
    actual smooth density; it is not a caller premise. *)
Definition current_smoothing_ambient_variation_integral epsilon
    (hEpsilon:0<epsilon) (f:X->R):R:=
  @radon_positive_compact_integral R XT
    (@current_ambient_variation R h2 n m (Smooth epsilon) (hSmooth epsilon hEpsilon))
    (@current_ambient_variation_laws R h2 n m (Smooth epsilon) (hSmooth epsilon hEpsilon)).1
    (@current_ambient_variation_laws R h2 n m (Smooth epsilon) (hSmooth epsilon hEpsilon)).2 f.

(** Source for [current_smoothing_weak_variation]: the literal
    weak convergence ||T_epsilon|| to ||T|| stated
    and proved in Federer 4.1.18, p. 375.
    The estimate holds for all small positive scales,
    all original compact positive scalar tests, arbitrary
    noncompact support and infinite total mass. *)
Theorem current_smoothing_weak_variation (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  forall eta:R,0<eta ->exists r:R,0<r /\
    forall epsilon:R,forall hEpsilon:0<epsilon,epsilon<r ->
      `|current_smoothing_ambient_variation_integral hEpsilon f-D f|<eta.
Proof.
move=>hF.
pose G epsilon:=if pselect (0<epsilon) is left he then
  current_smoothing_ambient_variation_integral he f else 0.
have hGValue epsilon (he:0<epsilon):
    G epsilon=current_smoothing_ambient_variation_integral he f.
  rewrite /G;case:pselect=>[h|hNot];last exact:(False_ind _ (hNot he)).
  have hEqual:h=he:=Prop_irrelevance _ _;by rewrite hEqual.
have hGGauge epsilon (he:0<epsilon):
    is_distribution_variation_value NY values (action (Smooth epsilon)) f (G epsilon)%:E.
  rewrite hGValue.
  exact:(@current_ambient_variation_original_gauge R h2 n m (Smooth epsilon)
    (hSmooth epsilon he) f hF).
have hTGauge:=@current_ambient_variation_original_gauge R h2 n m T hT f hF.
have hWeak omega eps:0<eps ->exists r:R,0<r /\
    forall epsilon:R,0<epsilon ->epsilon<r ->
      `|action (Smooth epsilon) omega-action T omega|<eps.
  exact:(@current_smoothing_weak_test_limit R h2 n m phi family hPhi hFamily T omega eps).
have hD:=@radon_positive_compact_integral_daniell R XT mu hm hr.
have hUpper eta:0<eta ->exists r:R,0<r /\
    forall epsilon:R,0<epsilon ->epsilon<r ->G epsilon<=D f+eta.
  move=>hEta.
  have [g [K [r [hK [hr0 [hFamilyG hUniform]]]]]]:=
    @positive_compact_smoothing_family_exists R n phi family hPhi hFamily f hF.1 hF.2.
  pose K0:set XT:=K `|` real_function_support f.
  have hK0:compact K0:=compactU hK hF.1.2.
  pose chi:=@CompactCutoff.value R XT K0 (@metric_hausdorff R XT)
    (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n)
      NX hNX) hK0.
  have hChi:is_compact_cutoff K0 chi:=@CompactCutoff.laws R XT K0
    (@metric_hausdorff R XT)
    (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n)
      NX hNX) hK0.
  have hChiPositive:positive_function_lattice
      (@compactly_supported_continuous_functions R XT) chi.
    split;first exact:compact_cutoff_function hChi.
    by move=>x;exact:(andP (compact_cutoff_range hChi x)).1.
  have hLP:=positive_function_lattice_laws
    (@compactly_supported_continuous_functions_lattice R XT).
  have hDChi:0<=D chi:=monotone_daniell_integral_nonnegative hLP hD
    hChiPositive hChiPositive.2.
  have hDen:0<D chi+1 by lra.
  pose delta:=eta/(D chi+1).
  have hDelta:0<delta by rewrite /delta divr_gt0.
  have [d [hd hSmall]]:=hUniform delta hDelta.
  exists (Order.min r d);split;first by rewrite lt_min hr0 hd.
  move=>epsilon he heSmall.
  have hR:Order.min r d<=r by rewrite ge_min lexx.
  have hD0:Order.min r d<=d by rewrite ge_min lexx orbT.
  have her:=lt_le_trans heSmall hR.
  have hed:=lt_le_trans heSmall hD0.
  have [hGCompact [hGPositive [hConv hGOff]]]:=hFamilyG epsilon he her.
  have hGP:positive_function_lattice
      (@compactly_supported_continuous_functions R XT) (g epsilon).
    by split.
  have hDifference:forall x,`|f x-g epsilon x|<=delta.
    move=>x;rewrite distrC;exact:ltW (hSmall epsilon he her hed x).
  have hError:=@compact_daniell_fixed_support_uniform_bound R XT K0 chi hChi D hD
    f (g epsilon) delta hF hGP (ltW hDelta) hDifference
    (fun x hx=>real_function_zero_off_support
      (fun hs=>hx (or_intror hs)))
    (fun x hx=>hGOff x (fun hk=>hx (or_introl hk))).
  have hTG:=@current_ambient_variation_original_gauge R h2 n m T hT (g epsilon) hGP.
  have hActual:=@current_smoothing_original_gauge_upper R h2 n m phi family hPhi hFamily
    epsilon he T f (g epsilon) (D (g epsilon)) (G epsilon)%:E hConv hTG (hGGauge epsilon he).
  rewrite lee_fin in hActual.
  have hIntegralBound:D (g epsilon)<=D f+delta*D chi.
    have hReverse:`|D (g epsilon)-D f|<=delta*D chi by rewrite distrC.
    have hRaw:=le_trans (ler_norm (D (g epsilon)-D f)) hReverse;lra.
  have hDenNonzero:D chi+1!=0 by rewrite (gt_eqF hDen).
  have hCancel:delta*(D chi+1)=eta by rewrite /delta divfK //.
  rewrite mulrDr mulr1 in hCancel;lra.
move=>eta hEta.
have [r [hr0 hLimit]]:=@distribution_variation_parameter_squeeze R X Y NY DT values
  (fun epsilon=>action (Smooth epsilon)) (action T) f G (D f)
  hGGauge hTGauge hWeak hUpper eta hEta.
exists r;split=>// epsilon he her.
have hBound:=hLimit epsilon he her.
by rewrite hGValue in hBound.
Qed.
End CurrentSmoothingWeakVariation.
