(** Federer (1969), 4.1.18, p. 376: the
    original iteration step chooses normal R_i,S_i,
    smooths R_i inside the printed support allowance,
    and subtracts its actual smooth L1 coefficient and
    boundary S_i. Two independent small flat errors
    give the displayed new residual bound. Finite
    mass of the original flat input is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology ring.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary CurrentBoundarySupport NormalCurrentsUP NormalCurrentBoundary
  CurrentMassSealed CurrentFlatNorm CurrentFlatFiniteArithmetic
  CurrentFlatCompactMonotone FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure
  SmoothCompactSet EuclideanClosedSupportTube CurrentCompactTubeIndex
  CurrentFlatNormalCostApproximation CurrentNormalSmoothingScale
  CurrentSmoothingOperators CurrentSmoothingNormality CurrentSmoothingSupportTube
  CurrentSmoothingFlatError CurrentSmoothingCompactCoefficient
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingPeel.
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
Local Notation Next:=(@current_space R h2 n Full hFull m.+1).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation image:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation bd:=(@current_boundary R h2 n m Full hFull).
Local Notation M:=(@CurrentMass.value R h2 n m Full hFull).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 Full hFull).
Local Notation N:=(@current_normal_mass R h2 n Full hFull m).
Local Notation F K:=(@current_flat_norm R h2 n m Full hFull K).
Local Notation flat K:=(@is_flat_current_supported_in R h2 n m Full hFull K).
Local Notation normal K:=(@normal_currents_supported_in R h2 n Full hFull m K).
Local Notation normalNext K:=(@normal_currents_supported_in R h2 n Full hFull m.+1 K).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).

(** Source for [current_flat_smoothing_peel]: the
    normal choices, actual smoothing coefficient, common
    compact support, independent price allowance and small
    flat residual in Federer 4.1.18, p. 376.
    Substituting r=2^(-i-1)delta and eta=2^(-i-3)delta
    gives the literal support and residual budgets.
    Empty K and every ambient and current degree remain. *)
Theorem current_flat_smoothing_peel (K:smooth_compact_set hNX Full)
    (T:C) (r eta zeta:R):
  flat K T->0<r->0<eta->0<zeta->
  let E:=@current_compact_closed_tube_index R n Full K r (fun _ _=>Logic.I) in
  exists A:C,exists S:Next,exists epsilon:R,exists f:V,exists xi:W,
    normal K A /\normalNext K S /\
    (F K (T-A-bd S)<eta%:E)%E /\
    (M A+NextM S<F K T+zeta%:E)%E /\
    0<epsilon /\epsilon<=r /\(epsilon%:E*N A<eta%:E)%E /\
    value xi=(fun x:UT=>vv f (set_val x)) /\
    Smooth A epsilon=image xi /\
    (forall x:UT,~smooth_compact_carrier E (set_val x)->value xi x=0) /\
    ((size xi)%:E<=M A)%E /\
    flat E (T-image xi-bd S) /\
    (F E (T-image xi-bd S)<(2*eta)%:E)%E /\
    ((size xi)%:E+NextM S<F K T+zeta%:E)%E.
Proof.
move=>hFlat hr hEta hZeta E.
have[A [S [hA [hS [hResidual hCost]]]]]:=
  @current_flat_normal_cost_approximation R h2 n m Full hFull K T hFlat
    eta zeta hEta hZeta.
have[epsilon [hEpsilon [hRadius hSmall]]]:=
  @current_normal_smoothing_scale R h2 n m Full hFull A r eta hA.1 hr hEta.
have hKE:smooth_compact_carrier K `<=` smooth_compact_carrier E.
  exact:(@current_compact_closed_tube_index_includes R n Full K r
    (fun _ _=>Logic.I) (ltW hr)).
have hTube:@euclidean_closed_support_tube R n
    (@current_support R h2 n Full hFull m A) epsilon `<=` smooth_compact_carrier E.
  exact:(@euclidean_closed_support_tube_mono R n
    (@current_support R h2 n Full hFull m A) (smooth_compact_carrier K)
    epsilon r hA.2 hRadius).
have[f [xi [hValue [hImage [hOff hSize]]]]]:=
  @current_smoothing_compact_coefficient_exists R h2 n m phi family hPhi hFamily
    epsilon hEpsilon A E hTube.
pose Q:=Smooth A epsilon.
have hNormalQ:@is_normal_current R h2 n Full hFull m Q.
  exact:(@current_smoothing_normal R h2 n phi family hPhi hFamily epsilon hEpsilon
    m A hA.1.2).
have hSupportQ:@current_support R h2 n Full hFull m Q `<=` smooth_compact_carrier E.
  move=>x hx;exact:(hTube x (@current_smoothing_support_tube R h2 n m
    phi family hPhi hFamily epsilon hEpsilon A x hx)).
have hQFlat:flat E Q.
  exact:(@supported_normal_current_is_flat R h2 n m Full hFull E Q
    (conj hNormalQ hSupportQ)).
have hTFlat:flat E T.
  exact:(@flat_current_compact_monotone R h2 n m Full hFull K E hKE T hFlat).
have hBoundaryNormal:=@normal_current_boundary R h2 n Full hFull m S hS.1.
have hBoundarySupport:@current_support R h2 n Full hFull m (bd S) `<=` smooth_compact_carrier E.
  move=>x hx;apply:hKE;apply:hS.2.
  exact:(@current_boundary_support_subset R h2 n m Full hFull S x hx).
have hBoundaryFlat:flat E (bd S).
  exact:(@supported_normal_current_is_flat R h2 n m Full hFull E (bd S)
    (conj hBoundaryNormal hBoundarySupport)).
pose G:=@flat_current_subspace R h2 n m Full hFull E.
have hNextFlat:flat E (T-image xi-bd S).
  rewrite -hImage.
  exact:(@subspace_sub R C G _ _
    (@subspace_sub R C G T Q hTFlat hQFlat) hBoundaryFlat).
pose D:=T-A-bd S.
have hD:(F E D<eta%:E)%E.
  exact:(le_lt_trans (@current_flat_compact_monotone R h2 n m Full hFull K E hKE D)
    hResidual).
have hQA:(F E (Q-A)<eta%:E)%E.
  exact:(le_lt_trans (@current_smoothing_flat_error R h2 n m phi family hPhi hFamily
    epsilon hEpsilon A E hTube) hSmall).
have hQAFinite:(F E (Q-A)< +oo)%E:=lt_trans hQA (ltry eta).
have hNeg:=@current_flat_finite_negate R h2 n m Full hFull E (Q-A) hQAFinite.
rewrite opprB in hNeg.
have hAQ:(F E (A-Q)<eta%:E)%E by rewrite hNeg.
have hTriangle:=@current_flat_finite_triangle R h2 n m Full hFull E D (A-Q)
  (lt_trans hD (ltry eta)) (lt_trans hAQ (ltry eta)).
have hIdentity:D+(A-Q)=T-Q-bd S.
  by rewrite /D addrA [T-A-bd S+A]addrAC subrK addrAC.
rewrite hIdentity /Q hImage in hTriangle.
have hResidualNext:(F E (T-image xi-bd S)<(2*eta)%:E)%E.
  apply:(le_lt_trans hTriangle).
  have hSum:=lteD hD hAQ.
  have hDouble:eta+eta= 2*eta by ring.
  by rewrite -EFinD hDouble /Q hImage in hSum.
have hPrice:((size xi)%:E+NextM S<F K T+zeta%:E)%E.
  exact:(le_lt_trans (leeD hSize (lexx (NextM S))) hCost).
exists A,S,epsilon,f,xi.
repeat split=>//.
Qed.
End SmoothingPeel.
