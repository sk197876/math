(** Federer (1969), 4.1.18, p. 375: both
    original smoothing operators have support in
    {x:dist(x,spt T)<=epsilon}. The closed-tube
    definition also retains an empty support.
    Compactness follows when T is compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentWholeSupportClosed CurrentScalarAverageSupport
  CurrentTranslations CurrentTranslationChain CurrentTranslationSupportTube
  CurrentSmoothingOperators CurrentSmoothingTranslationAverage CurrentSmoothingDeformationUP
  EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm SmoothingKernelUP SmoothingDilationUP
  SmoothingReflectedWeight EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothingSupportTube.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n))).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Variable T:@current_space R h2 n Full hFull m.
Local Notation Support:=(@current_support R h2 n Full hFull m T).
Local Notation Tube:=(@euclidean_closed_support_tube R n Support epsilon).
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily T epsilon).
Local Notation w:=(fun z:X=>family epsilon (-z)).

(** Source for [current_smoothing_support_tube]: the
    original support bound for T_epsilon, Federer
    4.1.18, p. 375, for every current T. *)
Theorem current_smoothing_support_tube:
  @current_support R h2 n Full hFull m Smooth `<=` Tube.
Proof.
apply:(@current_scalar_average_support R h2 n m X
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) w
  (fun z=>@current_translation_pushforward R h2 n m z T) Smooth
  (@current_smoothing_translation_average R h2 n m phi family hPhi hFamily
    epsilon hEpsilon T) Tube).
- apply:euclidean_closed_support_tube_norm_closed.
  exact:current_whole_support_closed.
- move=>z hz.
  have hRadius:NX z<=epsilon.
    case:(leP (NX z) epsilon)=>// hFar.
    exfalso;apply:hz.
    exact:(@smoothing_reflected_weight_off R n phi family hPhi hFamily
      epsilon hEpsilon z hFar).
  exact:(@current_translation_support_tube R h2 n m T z epsilon hRadius).
Qed.

(** Source for [current_smoothing_deformation_support_tube]:
    the original support bound for H_epsilon T,
    Federer 4.1.18, p. 375, follows from
    its independent literal averaged action. *)
Theorem current_smoothing_deformation_support_tube
    (Q:@current_space R h2 n Full hFull (1+m)%N):
  @is_current_smoothing_deformation R h2 n m family epsilon T Q ->
  @current_support R h2 n Full hFull (1+m)%N Q `<=` Tube.
Proof.
move=>hQ.
apply:(@current_scalar_average_support R h2 n (1+m)%N X
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) w
  (fun z=>@current_translation_chain R h2 n m z T) Q hQ Tube).
- apply:euclidean_closed_support_tube_norm_closed.
  exact:current_whole_support_closed.
- move=>z hz.
  have hRadius:NX z<=epsilon.
    case:(leP (NX z) epsilon)=>// hFar.
    exfalso;apply:hz.
    exact:(@smoothing_reflected_weight_off R n phi family hPhi hFamily
      epsilon hEpsilon z hFar).
  exact:(@current_translation_chain_support_tube R h2 n m T z epsilon hRadius).
Qed.

(** Source for [current_smoothing_compact]: a compact
    original current has compact smoothing support,
    as used repeatedly in 4.1.18, pp. 375–376. *)
Theorem current_smoothing_compact:
  @compact XT Support ->@compact XT (@current_support R h2 n Full hFull m Smooth).
Proof.
move=>hCompact.
exact:(@subclosed_compact XT _ _
  (@current_whole_support_closed R h2 n m hFull Smooth)
  (@euclidean_closed_support_tube_norm_compact R n Support epsilon hCompact)
  current_smoothing_support_tube).
Qed.
End CurrentSmoothingSupportTube.
