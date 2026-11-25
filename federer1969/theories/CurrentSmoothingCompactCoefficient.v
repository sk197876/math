(** Federer (1969), 4.1.18, p. 376: the
    smoothed normal approximant has an actual compact smooth
    coefficient xi_i in the original Omega_m, with
    integral mass no greater than M(R_i). This
    adapter uses the literal kernel density, its exact
    support tube and the previously specified density current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentMassSealed CurrentDensityUniqueness CurrentSmoothLebesgue
  CurrentSmoothLebesgueFullRepresentation CurrentOpenDensityActionUnique
  CurrentSmoothingOperators CurrentSmoothingSmoothDensity CurrentSmoothingMass
  CurrentSmoothingDensityCarrier EuclideanClosedSupportTube SmoothCompactSet
  SmoothingKernelUP SmoothingDilationUP EuclideanLebesgueDimensions EuclideanOpenDomainMeasure
  EuclideanFullDomainMeasure CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorSmoothField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactCoefficient.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation UT:=(current_domain R n Full).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation image:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation M:=(@CurrentMass.value R h2 n m Full hFull).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).

(** Source for [current_smoothing_compact_coefficient_exists]:
    the actual compact smooth xi_i and its original
    mass bound in the construction of Federer 4.1.18,
    p. 376. The current may have infinite mass;
    finite mass and normality enter only when this
    supporting theorem is applied to the chosen R_i. *)
Theorem current_smoothing_compact_coefficient_exists
    (T:C) (K:smooth_compact_set hNX Full)
    (hTube:@euclidean_closed_support_tube R n
      (@current_support R h2 n Full hFull m T) epsilon `<=` smooth_compact_carrier K):
  exists f:V,exists xi:W,
    value xi=(fun x:UT=>vv f (set_val x)) /\
    Smooth T epsilon=image xi /\
    (forall x:UT,~smooth_compact_carrier K (set_val x)->value xi x=0) /\
    ((size xi)%:E<=M T)%E.
Proof.
have[f [hAction hKernel]]:=@current_smoothing_smooth_density_exists R h2 n m
  phi family hPhi hFamily epsilon hEpsilon T.
have hOff:forall x,Full x->~smooth_compact_carrier K x->vv f x=0.
  move=>x _ hx;apply:(@current_smoothing_density_zero_off_tube R h2 n m
    phi family hPhi hFamily epsilon hEpsilon T f hKernel x).
  move=>h;exact:(hx (hTube x h)).
have[xi hValue]:=@compact_summable_multivector_smooth_field R h2 n m
  Full hFull f K hOff.
have hSmooth:Smooth T epsilon=@current_smooth_lebesgue_map R h2 n m f.
  exact:(@current_density_action_unique R h2 n m (@euclidean_lebesgue_measure R n)
    (vv f) (Smooth T epsilon) (@current_smooth_lebesgue_map R h2 n m f)
    hAction (current_smooth_lebesgue_action f)).
have hXi:=@compact_summable_multivector_current_representation R h2 n m Full hFull xi.
rewrite hValue in hXi.
have hDensity:=@current_smooth_lebesgue_full_representation R h2 n m f.
have hEqual:image xi=@current_smooth_lebesgue_map R h2 n m f.
  exact:(@current_open_density_action_unique R h2 n m Full hFull
    (@euclidean_open_domain_measure R n Full)
    (fun x:UT=>vv f (set_val x)) (image xi)
    (@current_smooth_lebesgue_map R h2 n m f) hXi hDensity).
have hImage:Smooth T epsilon=image xi:=eq_trans hSmooth (esym hEqual).
exists f,xi;split;first exact:hValue.
split;first exact:hImage.
split.
- move=>x hx;rewrite hValue;exact:(hOff (set_val x) Logic.I hx).
- rewrite -(@compact_summable_multivector_current_mass R h2 n m Full hFull xi)
    -hImage.
  exact:(@current_smoothing_mass_bound R h2 n m phi family hPhi hFamily epsilon hEpsilon T).
Qed.
End CompactCoefficient.
