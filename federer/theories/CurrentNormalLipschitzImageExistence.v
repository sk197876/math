(** Federer (1969), 4.1.14, p. 370: construct the
    original compact Lipschitz image first for a normal
    current. All allowed source neighbourhoods, flat
    representatives and K-only bounded smooth families
    satisfy the original convergence condition. Only the
    actual restriction and the preceding normal limits
    occur inside the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP SmoothCompactSet SmoothCompactSetExtensionality
  CurrentSpaces NormalCurrentsUP FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximation
  CurrentCompactSmoothApproximationOriginal CurrentApproximationOpenRestriction
  CurrentOpenRestriction CurrentOpenRestrictionSupport CurrentOpenRestrictionNormal
  CurrentFlatNeighbourhoodRepresentative CurrentCompactPushforwardAlgebra
  CurrentSmoothApproximationUP CurrentNormalSmoothApproximationImage CurrentNormalApproximationNeighbourhoodComparison
  CurrentFlatSequenceComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalLipschitzImageExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation Image:=(@is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal K).

(** Source for [current_normal_lipschitz_image_exists]: the
    normal-current existence assertion and full original
    approximation law in Federer 4.1.14, p. 370.
    Every flat representative under inclusion is identified
    with the actual restriction of T before its normality
    is derived. No normality of that representative is
    added to the caller's hypotheses. *)
Theorem current_normal_lipschitz_image_exists
    (T:@current_space R h2 n U hU m)
    (hNormal:@is_normal_current R h2 n U hU m T)
    (hSupport:@current_support R h2 n U hU m T `<=` smooth_compact_carrier K):
  exists Q:@current_space R h2 nu V hV m,
    @is_normal_current R h2 nu V hV m Q /\Image T Q.
Proof.
have[L [Z0 [g [hLeast hApprox]]]]:=
  @current_lipschitz_compact_smooth_approximation_exists R n nu
    U V hU hV K f hLocal hImage.
pose hZ0:=current_compact_smooth_domain_open hApprox.
pose hZ0U:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z0 g hApprox.
pose hKZ0:=current_compact_smooth_domain_contains hApprox.
pose K0:=@current_compact_index_in_open R n U Z0 K hKZ0.
pose S0:=@current_open_restriction R h2 n m Z0 U hZ0 hU hZ0U T.
pose hTS0:=fun x (hx:@current_support R h2 n U hU m T x)=>hKZ0 x (hSupport x hx).
pose hN0:=@current_normal_neighbourhood_restriction R h2 n Z0 U hZ0 hU hZ0U
  m T hNormal hTS0.
have hS0:@current_support R h2 n Z0 hZ0 m S0 `<=` smooth_compact_carrier K0.
  move=>x hx;exact:hSupport x
    (@current_open_restriction_support_subset R h2 n m Z0 U hZ0 hU hZ0U T x hx).
pose hG:=@current_compact_smooth_original_approximation R n nu U V K f L Z0 g hApprox.
pose hFImage0:=fun x (hx:Z0 x)=>hImage x (hZ0U x hx).
pose hFLocal0:=@metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U Z0 f hZ0U hLocal.
have[Q [hNQ hAll]]:=@current_normal_smooth_approximation_image R h2 n nu m
  Z0 V hZ0 hV K0 f hFImage0 hFLocal0 g hG S0 hN0 hS0.
have hIndex:@current_lipschitz_compact_image R n nu Z0 V hZ0
    f hFImage0 hFLocal0 K0=fK.
  apply:smooth_compact_set_extensionality;by [].
rewrite hIndex in hNQ.
exists Q;split;first exact:hNQ.1.
split;first exact:(@supported_normal_current_is_flat R h2 nu m V hV fK Q hNQ).
move=>E hInterior Z1 hZ1 hZ1U hKZ1 S1 hS1 hInclusion q hQ.
pose K1:=@current_compact_index_in_open R n U Z1 K hKZ1.
pose S1Original:=@current_open_restriction R h2 n m Z1 U hZ1 hU hZ1U T.
have hS1Identity:S1=S1Original.
  exact:(@current_flat_representative_is_open_restriction R h2 n m U Z1
    hU hZ1 hZ1U K hKZ1 T S1 hS1 hInclusion).
pose compact1:=@flat_supported_current_compact R h2 n m Z1 hZ1 K1 S1 hS1.
pose u:=fun i=>@current_compact_map_pushforward R h2 n nu Z0 V hZ0 hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m S0 hN0.2.
pose v:=fun i=>@current_compact_map_pushforward R h2 n nu Z1 V hZ1 hV
  (q i) (current_smooth_approximation_image hQ i)
  (current_smooth_approximation_class hQ i) m S1 compact1.
apply:(@current_flat_sequence_limit_compare R h2 nu m V hV E u v Q
  (hAll g hG E hInterior)).
move=>epsilon hEpsilon.
have[N hN]:=@current_normal_approximation_neighbourhoods_compare R h2 n nu m
  U V hU hV f hImage hLocal K T hNormal hSupport
  Z1 Z0 hZ1 hZ0 hZ1U hZ0U hKZ1 hKZ0 q g hQ hG E hInterior epsilon hEpsilon.
pose hT1:=fun x (hx:@current_support R h2 n U hU m T x)=>hKZ1 x (hSupport x hx).
pose hN1:=@current_normal_neighbourhood_restriction R h2 n Z1 U hZ1 hU hZ1U
  m T hNormal hT1.
have hImage1 i:v i=@current_compact_map_pushforward R h2 n nu Z1 V hZ1 hV
    (q i) (current_smooth_approximation_image hQ i)
    (current_smooth_approximation_class hQ i) m S1Original hN1.2.
  exact:(@current_compact_map_pushforward_congruence R h2 n nu Z1 V hZ1 hV
    (q i) (current_smooth_approximation_image hQ i)
    (current_smooth_approximation_class hQ i) m S1 S1Original compact1 hN1.2 hS1Identity).
exists N=>i hNi.
have hSmall:=@hN i i hNi hNi.
by rewrite -(hImage1 i) in hSmall.
Qed.
End CurrentNormalLipschitzImageExistence.
