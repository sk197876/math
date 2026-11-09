(** Federer (1969), 3.4.4, p. 318: the
    actual homeomorphism between the two original Cantor sets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  BinaryCantorCodingUP BinaryCantorMatchingUP BinaryCantorMatchingExistence
  BinaryCantorMatchingUniqueness BinaryCantorHolder BinaryCantorScalePowers
  HolderRelativeContinuity MetricSubsetBackground MetricSubsetCorestriction HomeomorphismUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_subset_correspondence]:
    phi regarded as a map between the original subspaces,
    3.4.4, p. 318. The proof of image containment
    merely permits the existing subspace corestriction. *)
Definition binary_cantor_subset_correspondence (R:realType)
    (A B:set (real_line_metric R)) I J phi
    (hPhi:is_binary_cantor_correspondence A B I J phi):
    metric_subset A->metric_subset B:=
  @metric_subset_corestriction R [the metricType R of real_line_metric R]
    (metric_subset A) B (fun x=>phi (val x))
    (fun x=>binary_cantor_correspondence_maps hPhi (set_valP x)).

(** Source for [binary_cantor_correspondences_homeomorphism]:
    the induced homeomorphism in 3.4.4, p. 318.
    The sharp Holder estimates prove actual relative continuity
    in both directions; the proved address identities give
    both cancellations. No homeomorphism law is assumed. *)
Theorem binary_cantor_correspondences_homeomorphism (R:realType) (alpha beta:R)
    JA HA I a JB HB J b A B phi psi
    (hPhi:is_binary_cantor_correspondence A B I J phi)
    (hPsi:is_binary_cantor_correspondence B A J I psi):
  0<alpha ->alpha<1 ->0<beta ->beta<1 ->
  is_binary_original_coding (real_power 2 (-alpha^-1)) JA HA I a ->
  is_binary_original_coding (real_power 2 (-beta^-1)) JB HB J b ->
  is_special_interval_tree_limit HA A ->is_special_interval_tree_limit HB B ->
  is_homeomorphism_with_inverse
    (binary_cantor_subset_correspondence hPhi)
    (binary_cantor_subset_correspondence hPsi).
Proof.
move=>hAlpha hAlphaUpper hBeta hBetaUpper hI hJ hA hB.
have [hRho hGap]:=binary_cantor_scale_bounds hAlpha hAlphaUpper.
have [hSigma hTargetGap]:=binary_cantor_scale_bounds hBeta hBetaUpper.
have hForward:continuous (fun x:metric_subset A=>(phi (val x):real_line_metric R)).
  apply:(@holder_real_subset_continuous R A phi
    (real_power (1-2*real_power 2 (-alpha^-1)) (-(alpha/beta))) (alpha/beta)).
  - exact:real_power_strictly_positive _ hGap.
  - by rewrite divr_gt0.
  - exact:(@binary_cantor_printed_holder_bound R alpha beta JA HA I a JB HB J b A B phi
      hAlpha hAlphaUpper hBeta hI hJ hA hPhi).
have hBackward:continuous (fun x:metric_subset B=>(psi (val x):real_line_metric R)).
  apply:(@holder_real_subset_continuous R B psi
    (real_power (1-2*real_power 2 (-beta^-1)) (-(beta/alpha))) (beta/alpha)).
  - exact:real_power_strictly_positive _ hTargetGap.
  - by rewrite divr_gt0.
  - exact:(@binary_cantor_printed_holder_bound R beta alpha JB HB J b JA HA I a B A psi
      hBeta hBetaUpper hAlpha hJ hI hB hPsi).
constructor.
- exact:metric_subset_corestriction_continuous hForward.
- exact:metric_subset_corestriction_continuous hBackward.
- move=>x;apply:val_inj.
  exact:(@binary_original_reverse_correspondence R (real_power 2 (-alpha^-1))
    (real_power 2 (-beta^-1)) JA HA I a JB HB J b A B phi psi hI hJ hA hB
    (andP hRho).1 (andP hRho).2 (andP hSigma).1 hTargetGap hPhi hPsi
    (val x) (set_valP x)).
- move=>y;apply:val_inj.
  exact:(@binary_original_reverse_correspondence R (real_power 2 (-beta^-1))
    (real_power 2 (-alpha^-1)) JB HB J b JA HA I a B A psi phi hJ hI hB hA
    (andP hSigma).1 (andP hSigma).2 (andP hRho).1 hGap hPsi hPhi
    (val y) (set_valP y)).
Qed.

(** Source for [binary_cantor_homeomorphism_exists]:
    existence of the induced homeomorphism in 3.4.4,
    p. 318, for the original two interval trees.
    Existence of both correspondences is proved before
    their topology and inverse laws are applied. *)
Theorem binary_cantor_homeomorphism_exists (R:realType) (alpha beta:R)
    JA HA I a JB HB J b A B:
  0<alpha ->alpha<1 ->0<beta ->beta<1 ->
  is_binary_original_coding (real_power 2 (-alpha^-1)) JA HA I a ->
  is_binary_original_coding (real_power 2 (-beta^-1)) JB HB J b ->
  is_special_interval_tree_limit HA A ->is_special_interval_tree_limit HB B ->
  exists phi psi,
  exists (hPhi:is_binary_cantor_correspondence A B I J phi)
    (hPsi:is_binary_cantor_correspondence B A J I psi),
  is_homeomorphism_with_inverse (binary_cantor_subset_correspondence hPhi)
    (binary_cantor_subset_correspondence hPsi).
Proof.
move=>hAlpha hAlphaUpper hBeta hBetaUpper hI hJ hA hB.
have [hRho hGap]:=binary_cantor_scale_bounds hAlpha hAlphaUpper.
have [hSigma hTargetGap]:=binary_cantor_scale_bounds hBeta hBetaUpper.
have [phi hPhi]:=@binary_original_cantor_correspondence_exists R
  (real_power 2 (-alpha^-1)) (real_power 2 (-beta^-1))
  JA HA I a JB HB J b A B hI hJ hA hB (andP hRho).1 hGap
  (ltW (andP hSigma).1) (ltW (andP hSigma).2).
have [psi hPsi]:=@binary_original_cantor_correspondence_exists R
  (real_power 2 (-beta^-1)) (real_power 2 (-alpha^-1))
  JB HB J b JA HA I a B A hJ hI hB hA (andP hSigma).1 hTargetGap
  (ltW (andP hRho).1) (ltW (andP hRho).2).
exists phi,psi,hPhi,hPsi.
exact:(@binary_cantor_correspondences_homeomorphism R alpha beta
  JA HA I a JB HB J b A B phi psi hPhi hPsi
  hAlpha hAlphaUpper hBeta hBetaUpper hI hJ hA hB).
Qed.
