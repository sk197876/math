(** Federer (1969), 4.1.23, p. 379: normal
    currents are approximated by actual smooth compact
    Lebesgue coefficients supported inside Int C. Reuse
    the preceding smoothing mass, flat-error, scale and
    coefficient-carrier laws. This full-space supporting step
    will be transported to the original open U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentSpaces CurrentVectorSpaces
  CurrentCoefficientNorms CurrentDomain SmoothCompactSet NormalCurrentsUP
  CurrentMassSealed CurrentFlatNorm CurrentFlatFiniteArithmetic
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CurrentNormalSmoothingScale CurrentSmoothingOperators CurrentSmoothingFlatError
  CurrentSmoothingCompactCoefficient CurrentCompactClosedTubeInside
  EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm
  SmoothingKernelSealed SmoothingDilationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormalSmoothCoefficient.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation FT := (current_domain R n Full).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation support := (@current_support R h2 n Full hFull m).
Local Notation E := (@current_vector_smooth_space R h2 n Full hFull m).
Local Notation ev := (@current_vector_smooth_value R h2 n Full hFull m).
Local Notation W := (@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value := (@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation image := (@compact_summable_multivector_current R h2 n m Full hFull).

(** Source for [normal_full_smooth_coefficient_approximation]:
    the smooth-density reduction of Federer 4.1.23,
    p. 379, with an actual compact carrier
    contained in Int C, no mass increase,
    and arbitrarily small original F_C error. The
    field is an actual original Omega representative,
    agreeing pointwise with a genuine smooth field. *)
Theorem normal_full_smooth_coefficient_approximation
    (K C : smooth_compact_set hNX Full) (T : Current) (delta : R) :
  (forall x, smooth_compact_carrier K x ->
    norm_domain_interior NX (smooth_compact_carrier C) x) ->
  @normal_currents_supported_in R h2 n Full hFull m K T -> 0<delta ->
  exists f : E, exists xi : W, exists L : smooth_compact_set hNX Full,
    value xi=(fun x : FT => ev f (set_val x)) /\
    (forall x, smooth_compact_carrier L x ->
      norm_domain_interior NX (smooth_compact_carrier C) x) /\
    (forall x : FT, ~smooth_compact_carrier L (set_val x) -> value xi x=0) /\
    (@current_flat_norm R h2 n m Full hFull C (T-image xi)%R<delta%:E)%E /\
    (M (image xi)<=M T)%E.
Proof.
move=> hKC hNormal hDelta.
pose O := @interior XT (smooth_compact_carrier C).
have hOpenO : @open XT O := open_interior _.
have hO (x : X) (hx : O x) : norm_domain_interior NX O x.
  apply: (norm_domain_interior_neighbourhood hNX O x).2.
  exact: (@open_nbhs_nbhs XT x O (conj hOpenO hx)).
have hKO : smooth_compact_carrier K `<=` O.
  move=> x hx.
  exact: (norm_domain_interior_neighbourhood hNX _ _).1 (@hKC x hx).
pose KO := @Build_smooth_compact_set R X NX hNX O (smooth_compact_carrier K)
  hKO (smooth_compact_is_compact K).
have [radius [hRadius hInside]] := @current_compact_closed_tube_inside_exists R n O hO KO.
have [epsilon [hEpsilon [hSmall hCost]]] := @current_normal_smoothing_scale
  R h2 n m Full hFull T radius delta hNormal.1 hRadius hDelta.
pose L := @Build_smooth_compact_set R X NX hNX Full
  (@euclidean_closed_support_tube R n (smooth_compact_carrier K) epsilon)
  (fun _ _ => Logic.I)
  (@euclidean_closed_support_tube_norm_compact R n (smooth_compact_carrier K)
    epsilon (smooth_compact_is_compact K)).
have hLO : smooth_compact_carrier L `<=` O.
  move=> x hx; apply: (@hInside x).
  exact: (@euclidean_closed_support_tube_mono R n (smooth_compact_carrier K)
    (smooth_compact_carrier K) epsilon radius (fun _ hy => hy) hSmall x hx).
have hTubeL : @euclidean_closed_support_tube R n (support T) epsilon
    `<=` smooth_compact_carrier L.
  exact: (@euclidean_closed_support_tube_mono R n (support T)
    (smooth_compact_carrier K) epsilon epsilon hNormal.2 (lexx epsilon)).
have hTubeC : @euclidean_closed_support_tube R n (support T) epsilon
    `<=` smooth_compact_carrier C.
  move=> x hx; exact: interior_subset (@hLO x (@hTubeL x hx)).
pose kernel := @SmoothingKernel.value R n.
pose family := @SmoothingDilation.value R n kernel.
pose hKernel := @SmoothingKernel.laws R n.
pose hFamily := @SmoothingDilation.laws R n kernel.
pose S := @current_smoothing R h2 n m kernel family hKernel hFamily T epsilon.
have [f [xi [hValue [hImage [hOff hMass]]]]] :=
  @current_smoothing_compact_coefficient_exists R h2 n m kernel family
    hKernel hFamily epsilon hEpsilon T L hTubeL.
have hBound := @current_smoothing_flat_error R h2 n m kernel family
  hKernel hFamily epsilon hEpsilon T C hTubeC.
have hError : (@current_flat_norm R h2 n m Full hFull C (S-T)%R<delta%:E)%E :=
  le_lt_trans hBound hCost.
have hFinite : (@current_flat_norm R h2 n m Full hFull C (S-T)%R< +oo)%E :=
  lt_trans hError (ltry delta).
have hNegate := @current_flat_finite_negate R h2 n m Full hFull C (S-T)%R hFinite.
have hIdentity : (T-image xi)= -(S-T) by rewrite /S hImage opprB.
exists f,xi,L; split; first exact: hValue.
split.
- move=> x hx.
  exact: (norm_domain_interior_neighbourhood hNX _ _).2 (@hLO x hx).
split; first exact: hOff.
split.
- by rewrite hIdentity hNegate.
- rewrite (@compact_summable_multivector_current_mass R h2 n m Full hFull xi).
  exact: hMass.
Qed.
End NormalSmoothCoefficient.
