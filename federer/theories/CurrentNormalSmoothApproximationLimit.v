(** Federer (1969), 4.1.14, p. 370: a normal current
    has a normal flat limit under every original smooth
    approximation. The common compact target E is arbitrary,
    and the finite derivative cap is required only on K.
    Use 4.1.13 for the Cauchy estimate and 4.1.12 for
    completeness; no limit representation is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet NormalCurrentsUP
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentPushforwardNormality CurrentPushforwardSupport CurrentSupportGeometry
  FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure CurrentSmoothApproximationUP
  CurrentSmoothApproximationSegments CurrentNormalSmoothApproximationCauchy
  CurrentNormalSmoothApproximationMass CurrentFlatSequenceLimitUP
  CurrentFlatSequenceLimits FlatCurrentCauchyLimit
  NormalCurrentWeakEventualBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalSmoothApproximationLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z:set X) (V:set Y).
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX Z.
Variable f:X->Y.
Hypothesis hImage:forall x,Z x->V (f x).
Hypothesis hf:norm_class_zero NX NY Z f.
Variable g:nat->X->Y.
Hypothesis hG:@is_current_smooth_approximation R n nu Z V K f g.
Variable T:@current_space R h2 n Z hZ m.
Hypothesis hNormal:@is_normal_current R h2 n Z hZ m T.
Hypothesis hSupport:@current_support R h2 n Z hZ m T `<=` smooth_compact_carrier K.
Arguments hSupport : clear implicits.
Variable E:smooth_compact_set hNY V.
Hypothesis hInterior:forall x,smooth_compact_carrier K x->
  norm_domain_interior NY (smooth_compact_carrier E) (f x).
Local Notation u:=(fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m T hNormal.2).

(** Source for [current_normal_smooth_approximation_eventual_support]:
    every sufficiently late image lies in the prescribed E,
    supporting Federer 4.1.14, p. 370. The affine comparison
    argument is used at one endpoint, with the original
    arbitrary compact E; no convexity of E is required. *)
Lemma current_normal_smooth_approximation_eventual_support:
  exists N:nat,forall i,(N<=i)%N->
    @current_support R h2 nu V hV m (u i) `<=` smooth_compact_carrier E.
Proof.
have[N hN]:=@current_smooth_approximation_segments R n nu Z V K f g g hG hG
  hImage hf E hInterior.
exists N=>i hNi y hy.
have[x hx <-]:=@current_pushforward_support_image R h2 n nu m Z V hZ hV
  T (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i)
  (@current_compact_map_proper R h2 n nu m Z V hZ T (g i)
    (current_smooth_approximation_image hG i)
    (norm_class_continuous (current_smooth_approximation_class hG i 0%N))
    hNormal.2) y hy.
have h:=hN i i hNi hNi x 0 (hSupport x hx) (lexx 0) ler01.
by rewrite subr0 scale1r scale0r addr0 in h.
Qed.

(** Source for [current_normal_smooth_approximation_limit]:
    the normal image sequence has an actual normal limit
    in F_(m,E)(V), Federer 4.1.14, p. 370. Completeness
    is applied only after its eventual support enters E.
    The original weak mass bounds prove limit normality. *)
Theorem current_normal_smooth_approximation_limit:
  exists Q:@current_space R h2 nu V hV m,
    @normal_currents_supported_in R h2 nu V hV m E Q /\
    @is_current_flat_sequence_limit R h2 nu m V hV E u Q.
Proof.
have[N hN]:=current_normal_smooth_approximation_eventual_support.
have hFlat i:(N<=i)%N->@is_flat_current_supported_in R h2 nu m V hV E (u i).
  move=>hNi;apply:(@supported_normal_current_is_flat R h2 nu m V hV E (u i)).
  split;last exact:hN i hNi.
  exact:(@current_pushforward_normal R h2 n nu Z V hZ hV (g i)
    (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m T
    (@current_compact_map_proper R h2 n nu m Z V hZ T (g i)
      (current_smooth_approximation_image hG i)
      (norm_class_continuous (current_smooth_approximation_class hG i 0%N))
      hNormal.2) hNormal).
have hCauchy:=@current_normal_smooth_approximation_cauchy R h2 n nu Z V hZ hV
  K f hImage hf g hG m T hNormal hSupport E hInterior.
have[Q [hQ hLimit]]:=@flat_current_eventual_cauchy_sequence_limit R h2 nu m V hV
  E u N hFlat hCauchy.
have[b [hb hMass]]:=@current_normal_smooth_approximation_mass_bound R h2 n nu
  Z V hZ hV K f g hG m T hNormal hSupport.
exists Q;split;last exact:hLimit.
exact:(@normal_current_weak_eventual_normal_bound R h2 nu m V hV E u Q b
  (@current_flat_sequence_limit_weak R h2 nu m V hV E u Q hLimit)
  (ex_intro _ N hN) hMass).
Qed.
End CurrentNormalSmoothApproximationLimit.
