(** Federer (1969), 4.1.14, p. 372: for an
    original normal current the conclusions of 4.1.13,
    pp. 369–370, hold with rho replaced by the
    common continuous Lebesgue-AE differential bound sigma.
    Use the original two affine chains, their exact
    support hull, the extended homotopy identities and
    the preceding flat decomposition. Degree zero is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP OpenLocalLipschitzCompact SmoothCompactSet
  CurrentDomain CurrentSpaces CurrentBoundary CurrentBoundarySupport CurrentSupportGeometry
  CurrentIntegrationCriterion NormalCurrentsUP NormalCurrentBoundary
  CompactRepresentedCurrentMass CurrentMassSealed NormalisedCurrentSealed
  FlatCurrentsUP CurrentNormalOriginalFlat CurrentLocallyFlatBoundary
  CurrentFlatLipschitzPushforwardSealed CurrentAffineSegmentHull
  CurrentAffineSegmentHullContinuous CurrentLipschitzAffineChainSealed
  CurrentLipschitzAffineChainSupport CurrentLipschitzAffineChainMass
  CurrentLipschitzAffineHomotopyFormula CurrentCompactMajorantApproximationUP
  CurrentFlatNorm CurrentFlatMassComparison CurrentFlatBoundary
  SummableRealFunctionUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzAffineFlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypotheses (hFImage:forall x,U x->V (f x)) (hGImage:forall x,U x->V (g x)).
Hypotheses (hFLocal:@is_locally_metric_lipschitz R XT YT U f)
  (hGLocal:@is_locally_metric_lipschitz R XT YT U g).
Variable sigma:X->R^o.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Hypotheses (hFMajorant:@is_current_ae_differential_majorant R n nu U f sigma)
  (hGMajorant:@is_current_ae_differential_majorant R n nu U g sigma).
Local Notation UT := (current_domain R n U).
Local Notation displacement := (fun x:UT=>NY (g (set_val x)-f (set_val x))).
Local Notation Weight k := (fun x:UT=>(displacement x*(sigma (set_val x))^+k)%R).
Local Notation fClass := (@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY
  U f hU hFLocal).
Local Notation gClass := (@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY
  U g hU hGLocal).

Section PositiveDegree.
Variable j:nat.
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hNormal:@is_normal_current R h2 n U hU j.+1 T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU j.+1 T x->
  V ((1-t)*:f x+t*:g x).
Local Notation hFlat := (@current_normal_original_flat R h2 n j.+1 U hU T hNormal).
Local Notation boundary := (@current_boundary R h2 n j U hU T).
Local Notation hFlatB := (@flat_current_boundary R h2 n j U hU T hFlat).
(** Source for [hBandB]: the boundary support is contained in spt T,
    Federer 4.1.7, p. 356, used in 4.1.14, p. 372. *)
Let hBandB:forall t x,0<=t<=1->@current_support R h2 n U hU j boundary x->
    V ((1-t)*:f x+t*:g x) :=
  fun t x ht hx=>@hBand t x ht (@current_boundary_support_subset R h2 n j U hU T x hx).
(** Source for [hC]: the original support-segment union lies in V,
    Federer 4.1.14, p. 372. *)
Let hC:@current_affine_segment_hull R h2 n nu j.+1 U hU f g T `<=` V.
Proof. by move=>y [t [x [ht [hx <-]]]];exact:(@hBand t x ht hx). Qed.
Local Notation C := (@current_continuous_affine_image_compact R h2 n nu j.+1
  U V hU f g fClass gClass T hNormal.2 hC).
Local Notation F := (@CurrentFlatLipschitzPushforward.value R h2 n nu j.+1
  U V hU hV f hFImage hFLocal T hFlat).
Local Notation G := (@CurrentFlatLipschitzPushforward.value R h2 n nu j.+1
  U V hU hV g hGImage hGLocal T hFlat).
Local Notation S := (@CurrentLipschitzAffineChain.value R h2 n nu j.+1 U V hU hV
  f g hFLocal hGLocal T hFlat hBand).
Local Notation B := (@CurrentLipschitzAffineChain.value R h2 n nu j U V hU hV
  f g hFLocal hGLocal boundary hFlatB hBandB).
Local Notation mu := (@NormalisedCurrent.measure R h2 n j.+1 U hU T hNormal.1.1).
Local Notation muB := (@NormalisedCurrent.measure R h2 n j U hU boundary hNormal.1.2).

(** Source for [current_lipschitz_affine_positive_flat_bound]:
    F_C(g#T-f#T) <= ||T||(|g-f|sigma^(j+1))
    + ||boundary T||(|g-f|sigma^j), Federer 4.1.14,
    p. 372, referring to 4.1.13, p. 369.
    C is exactly the original segment union over spt T;
    no global derivative constant replaces either weight. *)
Theorem current_lipschitz_affine_positive_flat_bound :
  (@current_flat_norm R h2 nu j.+1 V hV C (G-F)<=
    measure_lower_integral mu (real_total_integrand (Weight j.+1))+
    measure_lower_integral muB (real_total_integrand (Weight j)))%E.
Proof.
have hFormula:=@current_lipschitz_affine_homotopy_positive_formula R h2 n nu
  U V hU hV f g hFImage hGImage hFLocal hGLocal j T hFlat hBand.
have hS:@current_support R h2 nu V hV j.+2 S `<=` smooth_compact_carrier C.
  exact:(@current_lipschitz_affine_chain_support R h2 n nu j.+1 U V hU hV
    f g hFLocal hGLocal T hFlat hBand).
have hB:@current_support R h2 nu V hV j.+1 B `<=` smooth_compact_carrier C.
  move=>y hy.
  have[t [x [ht [hx hxy]]]]:=@current_lipschitz_affine_chain_support R h2 n nu j
    U V hU hV f g hFLocal hGLocal boundary hFlatB hBandB y hy.
  exists t,x;split;first exact:ht.
  split;last exact:hxy.
  exact:(@current_boundary_support_subset R h2 n j U hU T x hx).
have hBoundary:@current_support R h2 nu V hV j.+1
    (@current_boundary R h2 nu j.+1 V hV S) `<=` smooth_compact_carrier C.
  move=>y hy;apply:hS.
  exact:(@current_boundary_support_subset R h2 nu j.+1 V hV S y hy).
have hDifference:@current_support R h2 nu V hV j.+1 (G-F) `<=` smooth_compact_carrier C.
  rewrite hFormula.
  have hSum:=@current_support_linear_subset R h2 nu j.+1 V hV C 1
    (@current_boundary R h2 nu j.+1 V hV S) B hBoundary hB.
  by rewrite scale1r in hSum.
have hCost:=@current_flat_decomposition_lower_bound R h2 nu j.+1 V hV C
  (G-F) S hDifference hS.
have hResidual:(G-F)-@current_boundary R h2 nu j.+1 V hV S = B.
  by rewrite hFormula addrAC subrr add0r.
rewrite hResidual addeC in hCost.
have hFinite:=@compact_represented_current_finite_mass R h2 n j.+1 U hU
  T hNormal.1.1 hNormal.2.
have hNormalB:=@normal_current_boundary R h2 n U hU j T hNormal.
have hFiniteB:=@compact_represented_current_finite_mass R h2 n j U hU
  boundary hNormal.1.2 hNormalB.2.
have hFirst:=(@current_lipschitz_affine_chain_mass R h2 n nu j.+1 U V hU hV
  f g hFImage hGImage hFLocal hGLocal sigma hSigma hFMajorant hGMajorant
  T hFlat hFinite hBand).2 hNormal.1.1.
have hSecond:=(@current_lipschitz_affine_chain_mass R h2 n nu j U V hU hV
  f g hFImage hGImage hFLocal hGLocal sigma hSigma hFMajorant hGMajorant
  boundary hFlatB hFiniteB hBandB).2 hNormal.1.2.
exact:le_trans hCost (leeD hFirst hSecond).
Qed.
End PositiveDegree.

Section DegreeZero.
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hNormal:@is_normal_current R h2 n U hU 0%N T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU 0%N T x->
  V ((1-t)*:f x+t*:g x).
Local Notation hFlat := (@current_normal_original_flat R h2 n 0%N U hU T hNormal).
(** Source for [hC]: the original support-segment union lies in V,
    Federer 4.1.14, p. 372. *)
Let hC:@current_affine_segment_hull R h2 n nu 0%N U hU f g T `<=` V.
Proof. by move=>y [t [x [ht [hx <-]]]];exact:(@hBand t x ht hx). Qed.
Local Notation C := (@current_continuous_affine_image_compact R h2 n nu 0%N
  U V hU f g fClass gClass T hNormal.2 hC).
Local Notation F := (@CurrentFlatLipschitzPushforward.value R h2 n nu 0%N
  U V hU hV f hFImage hFLocal T hFlat).
Local Notation G := (@CurrentFlatLipschitzPushforward.value R h2 n nu 0%N
  U V hU hV g hGImage hGLocal T hFlat).
Local Notation S := (@CurrentLipschitzAffineChain.value R h2 n nu 0%N U V hU hV
  f g hFLocal hGLocal T hFlat hBand).
Local Notation mu := (@NormalisedCurrent.measure R h2 n 0%N U hU T hNormal.1.1).

(** Source for [current_lipschitz_affine_zero_flat_bound]:
    F_C(g#T-f#T) <= ||T||(|g-f|) in degree zero,
    Federer 4.1.14, p. 372, referring to
    4.1.13, p. 369. The displacement survives
    when sigma is zero: its zeroth power is one. *)
Theorem current_lipschitz_affine_zero_flat_bound :
  (@current_flat_norm R h2 nu 0%N V hV C (G-F)<=
    measure_lower_integral mu (real_total_integrand displacement))%E.
Proof.
have hFormula:=@current_lipschitz_affine_homotopy_zero_formula R h2 n nu
  U V hU hV f g hFImage hGImage hFLocal hGLocal T hFlat hBand.
have hS:@current_support R h2 nu V hV 1%N S `<=` smooth_compact_carrier C.
  exact:(@current_lipschitz_affine_chain_support R h2 n nu 0%N U V hU hV
    f g hFLocal hGLocal T hFlat hBand).
have hFinite:=@compact_represented_current_finite_mass R h2 n 0%N U hU
  T hNormal.1.1 hNormal.2.
have hMass:=(@current_lipschitz_affine_chain_mass R h2 n nu 0%N U V hU hV
  f g hFImage hGImage hFLocal hGLocal sigma hSigma hFMajorant hGMajorant
  T hFlat hFinite hBand).2 hNormal.1.1.
have hWeight:Weight 0%N=displacement by apply:funext=>x;rewrite expr0 mulr1.
rewrite hWeight in hMass.
rewrite hFormula.
apply:(le_trans (@current_flat_boundary_bound R h2 nu 0%N V hV C S)).
exact:le_trans (@current_flat_norm_le_mass R h2 nu 1%N V hV C S hS) hMass.
Qed.
End DegreeZero.
End CurrentLipschitzAffineFlatBound.
