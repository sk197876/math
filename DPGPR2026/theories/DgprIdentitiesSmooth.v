(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3;
    blueprint dgpr_blueprint.tex, lem:identities(div), first assertion,
    and the class-infinity assertions of lem:regularity: the maps U, W, R,
    Psi, rho and S are of class infinity on Omega_T, and so are B, eta,
    kappa, q, log S, log rho and log q.

    Class infinity is Federer's class of 3.1.11 on the open set
    Omega_T = {(t,x) : t < T} of R x R^n with the product inner product of
    Federer 1.7.11, [norm_class_all_orders hNT _ (dgpr_before T) _]. The
    logarithm is of class infinity on {r : 0 < r}, since its derivatives
    are the derivatives of [r |-> r^(-1)] (Federer 3.1.11, p. 223). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates ScalarInnerProduct ProductInner CompleteMetricUP
  VectorDaniellHypotheses PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasurableFunctionUP
  RadonMeasureUP MeasureVectorIntegralUP ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormDifferentialLocal NormOpenDomainLaws NormClassOneUP NormClassHigherUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormRegularity NormRegularityOperations
  NormRegularityBilinear ScalarNormalizationRegularity NormHigherCurveDerivativeUP RealExponentialUP
  RealExponentialSealed RealLogarithmDifferential ScalarDerivativeSequence ScalarReciprocalHigherDifferentials
  SmoothFunctionSpaceUP SmoothTestSpaces DistributionVariationUP FunctionLatticeUP CompactSupportFunctionUP.
From DPGPR Require Import DgprGrowthClasses DgprHeatKernel DgprHeatExtension DgprHeatExtensionSmooth DgprHeatSemiconvex
  DgprDifferentialCalculus DgprHeatJets DgprBackwardHeat DgprStanding DgprHeatObjects DgprIdentities
  DgprIdentitiesDivergence DgprBackwardHeatDecay.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ScalarClasses.
Variable R : realType.
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation L := (@RealExponential.logarithm R).

(** Source for [dgpr_positive_interior]: the half line {r : 0 < r} is
    open (Federer 3.1.1); supporting lem:regularity. *)
Lemma dgpr_positive_interior (a : R^o) : 0 < a -> norm_domain_interior A1 (fun t : R^o => 0 < t) a.
Proof.
move=> ha; exists a; split => // h hh.
have := ler_norm (- h); rewrite normrN => h1.
change (0 < a + h); lra.
Qed.

(** Source for [dgpr_logarithm_sequence]: F 0 = log and F (j+1) is the
    jth derivative of [r |-> r^(-1)]; supporting lem:regularity. *)
Definition dgpr_logarithm_sequence (j : nat) (a : R) : R^o :=
  if j is j'.+1 then scalar_reciprocal_derivative_coefficient j' a else L a.

(** Source for [dgpr_logarithm_norm_class]: the logarithm is of class
    infinity on {r : 0 < r}, Federer 3.1.11, p. 223, since
    D log(a)(h) = a^(-1) h and the derivatives of [r |-> r^(-1)] are
    known; supporting lem:regularity. *)
Lemma dgpr_logarithm_norm_class (k : nat) :
  norm_class hA hA (fun t : R^o => 0 < t) L k.
Proof.
have hF : forall j (a : R), 0 < a -> exists M : Hom R^o R^o,
    has_norm_differential A1 A1 (fun t : R^o => 0 < t) (dgpr_logarithm_sequence j) a M /\
    forall t, M t = t *: dgpr_logarithm_sequence j.+1 a.
  move=> [|j] a ha.
  - exists (real_logarithm_linear_term a); split.
      apply: (norm_differential_restrict (A := setT)) => //; first exact: dgpr_positive_interior.
      exact: real_logarithm_differential.
    move=> t; rewrite /= scalar_reciprocal_derivative_zero.
    by change (a^-1 * t = t * a^-1); rewrite mulrC.
  - exists (@scalar_coefficient_linear_map R R^o (scalar_reciprocal_derivative_coefficient j.+1 a)); split.
      apply: (norm_differential_restrict (A := fun t : R^o => t != 0)).
      + by move=> t ht; rewrite gt_eqF.
      + exact: dgpr_positive_interior.
      + exact: scalar_reciprocal_derivative_step (lt0r_neq0 ha).
    by move=> t.
exact ((@scalar_derivative_sequence_class_infinity R R^o A1 hA
  (fun j => @ContinuousMultilinear.space R j R^o R^o A1 A1 hA hA)
  (fun j => @ContinuousMultilinear.evaluation R j R^o R^o A1 A1 hA hA)
  (fun j => @ContinuousMultilinear.norm R j R^o R^o A1 A1 hA hA)
  (fun j => @ContinuousMultilinear.laws R j R^o R^o A1 A1 hA hA)
  (fun t : R => 0 < t) dgpr_logarithm_sequence hF) k).
Qed.
End ScalarClasses.

Section TimeClasses.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variable T : R.

(** Source for [dgpr_time_negation_map]: the linear map
    [(t,x) |-> -t] of R x R^n into R; supporting lem:identities(div). *)
Definition dgpr_time_negation_map (q : TX) : R^o := - q.1.

(** Source for [dgpr_time_negation_linear]: the map is linear;
    supporting lem:identities(div). *)
Lemma dgpr_time_negation_linear : linear dgpr_time_negation_map.
Proof.
move=> c a b; rewrite /dgpr_time_negation_map /=.
change (- (c * a.1 + b.1) = c * - a.1 + - b.1); ring.
Qed.

(** Source for [dgpr_time_negation_hom]: the map as an element of
    Hom(R x R^n, R); supporting lem:identities(div). *)
Definition dgpr_time_negation_hom : Hom TX R^o :=
  @HomMap R TX R^o dgpr_time_negation_map (asboolT dgpr_time_negation_linear).

(** Source for [dgpr_time_negation_bounded]: |t| <= |(t,x)| for the
    product inner product (Federer 1.7.11), hence the map is bounded;
    supporting lem:identities(div). *)
Lemma dgpr_time_negation_bounded : norm_bounded_linear NT A1 dgpr_time_negation_hom.
Proof.
exists 1; split => // q; rewrite mul1r.
change (`|- q.1| <= NT q); rewrite normrN; exact: dgpr_product_time_abs_le.
Qed.

(** Source for [dgpr_before_open]: Omega_T is open (mr:notation);
    supporting lem:identities(div). *)
Lemma dgpr_before_open (q : TX) : dgpr_before T q -> norm_domain_interior NT (dgpr_before T) q.
Proof. exact: dgpr_before_interior. Qed.

(** Source for [dgpr_time_to_go_class]: [(t,x) |-> T - t] is of class
    infinity on Omega_T, being affine (Federer 3.1.11); supporting
    lem:identities(div). *)
Lemma dgpr_time_to_go_class (k : nat) : norm_class hNT hA (dgpr_before T) (fun q : TX => T - q.1) k.
Proof.
have hL := norm_class_linear hNT hA k dgpr_before_open dgpr_time_negation_bounded.
have hC := norm_class_constant hNT hA (T : R^o) k dgpr_before_open.
apply: (norm_class_domain_agreement _ (norm_class_add hL hC)) => q _.
by change (- q.1 + T = T - q.1); rewrite addrC.
Qed.

(** Source for [dgpr_sqrt_time_to_go_class]: [(t,x) |-> (T - t)^(1/2)]
    is of class infinity on Omega_T, by the chain rule (Federer 3.1.11)
    and the smoothness of the square root on {r : 0 < r} (Federer 3.1.24);
    supporting lem:identities(div). *)
Lemma dgpr_sqrt_time_to_go_class (k : nat) :
  norm_class hNT hA (dgpr_before T) (fun q : TX => Num.sqrt (T - q.1)) k.
Proof.
apply: (norm_class_compose_on _ (dgpr_time_to_go_class k) (scalar_square_root_norm_class R k)).
by move=> q hq; change (0 < T - q.1); rewrite subr_gt0.
Qed.
End TimeClasses.

Section HeatObjectsSmooth.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation LOG := (@RealExponential.logarithm R).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation BD := (hom_inner_productP hCY (scalar_inner_productP R) heY).
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
Local Notation hND := (inner_norm_real_norm BD).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation hsep1 := (scalar_norm_separable R).
Local Notation hHc := (@dgpr_hom_space_complete R n Y CY hCY d eY heY).
Local Notation hDc := (@dgpr_dual_space_complete R Y CY hCY d eY heY).
Local Notation hHs := (@dgpr_hom_space_separable R n Y CY hCY d eY heY).
Local Notation hDs := (@dgpr_dual_space_separable R Y CY hCY d eY heY).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation hmu := (dgpr_standing_mu_measure hS).
Local Notation hups := (dgpr_standing_ups_measure hS).
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu := (dgpr_standing_mu_borel hS).
Local Notation hOups := (radon_open_measurable (dgpr_standing_ups_radon hS)).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu := (dgpr_standing_mu_mass hS).
Local Notation hMups := (dgpr_standing_ups_mass hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation W := (dgpr_heat_W hS).
Local Notation Rr := (dgpr_heat_R hS).
Local Notation Psi := (dgpr_heat_Psi hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation eta := (dgpr_heat_eta hS).
Local Notation kappa := (dgpr_heat_kappa hS).
Local Notation Q := (dgpr_heat_q hS).
Local Notation OmT := (dgpr_before T).

(** Source for [dgpr_identities_smooth_extensions]: blueprint
    lem:identities(div), first assertion, for U, W, R, Psi and rho: by
    (spt) they are [(t,x) |-> u(T - t, x)] for heat extensions u
    (def:heat_objects), hence of class infinity on Omega_T by
    lem:heat_extension(1) (DgprHeatExtensionSmooth.v). *)
Theorem dgpr_identities_smooth_extensions :
  [/\ norm_class_all_orders hNT hA OmT U, norm_class_all_orders hNT hNH OmT W,
      norm_class_all_orders hNT hA OmT Rr, norm_class_all_orders hNT hND OmT Psi &
      norm_class_all_orders hNT hA OmT rho].
Proof.
split.
- exact: (dgpr_heat_extension_backward_smooth hmu hZ1 hOmu hMmu hsep1 (dgpr_one_measurable hmu)
    (@dgpr_one_bound1 R n) T).
- exact: (dgpr_heat_extension_backward_smooth hmu hHc hOmu hMmu hHs (dgpr_standing_X_measurable hS)
    (fun y => dgpr_standing_K_norm hS (dgpr_standing_X_values hS y)) T).
- exact: (dgpr_heat_extension_backward_smooth hups hZ1 hOups hMups hsep1 (dgpr_one_measurable hups)
    (@dgpr_one_bound1 R n) T).
- exact: (dgpr_heat_extension_backward_smooth hups hDc hOups hMups hDs (dgpr_standing_dups_measurable hS)
    (dgpr_standing_dups_bound hS) T).
- exact: (dgpr_heat_extension_backward_smooth hmu0 hZ1 hOmu0 hMmu0 hsep1 (dgpr_one_measurable hmu0)
    (@dgpr_one_bound1 R n) T).
Qed.

(** Source for [dgpr_identities_smooth_S]: blueprint lem:identities(div),
    first assertion, for S = U + (T - t)^(1/2) R: sums and products of
    maps of class infinity are of class infinity (Federer 3.1.11). *)
Theorem dgpr_identities_smooth_S : norm_class_all_orders hNT hA OmT S.
Proof.
have [hU _ hR _ _] := dgpr_identities_smooth_extensions.
move=> k.
have h := norm_class_add (hU k) (norm_class_scalar_product (@dgpr_sqrt_time_to_go_class R n T k) (hR k)).
by apply: (norm_class_domain_agreement _ h) => q _.
Qed.

(** Source for [dgpr_identities_div_smooth]: blueprint lem:identities(div):
    U, W, R, Psi, S and rho are of class infinity on Omega_T, and
    div W_t(x) = Psi(t,x) and ||Psi(t,x)|| <= R(t,x) for (t,x) in
    Omega_T; the covector div W_t(x) is given by its values at y in Y as
    in DgprIdentitiesDivergence.v. *)
Theorem dgpr_identities_div_smooth :
  [/\ norm_class_all_orders hNT hA OmT U, norm_class_all_orders hNT hNH OmT W,
      norm_class_all_orders hNT hA OmT Rr, norm_class_all_orders hNT hND OmT Psi &
      norm_class_all_orders hNT hA OmT S /\ norm_class_all_orders hNT hA OmT rho] /\
  forall t x, t < T ->
    (forall (y : Y) (l : X -> Hom X Y), dgpr_differential_values NH (fun z => W (t, z)) x l ->
      \sum_(i < n) CY (l (eps i) (eps i)) y = Psi (t, x) y) /\
    ND (Psi (t, x)) <= Rr (t, x).
Proof.
have [hU hW hR hP hr] := dgpr_identities_smooth_extensions.
split; first by split => //; split => //; exact: dgpr_identities_smooth_S.
move=> t x ht; exact: (dgpr_identities_div hS x ht).
Qed.

(** Source for [dgpr_heat_S_inverse_smooth]: S^(-1) is of class infinity
    on Omega_T, since S > 0 there (lem:identities(bounds)) and
    [r |-> r^(-1)] is of class infinity on {r : r <> 0} (Federer 3.1.11,
    p. 223); supporting lem:regularity. *)
Lemma dgpr_heat_S_inverse_smooth : norm_class_all_orders hNT hA OmT (fun q => (S q)^-1).
Proof.
move=> k; apply: (norm_class_compose_on _ (dgpr_identities_smooth_S k) (scalar_reciprocal_norm_class R k)).
by move=> [t x] ht; exact: lt0r_neq0 (dgpr_identities_S_pos hS x ht).
Qed.

(** Source for [dgpr_regularity_smooth]: blueprint lem:regularity, the
    class-infinity assertions for B = S^(-1) W, eta = S^(-1) Psi,
    kappa = R / (2 (T - t)^(1/2) S) and q = rho / S on Omega_T, from
    the Leibniz formula and the chain rule (Federer 3.1.11). *)
Theorem dgpr_regularity_smooth :
  [/\ norm_class_all_orders hNT hNH OmT B, norm_class_all_orders hNT hND OmT eta,
      norm_class_all_orders hNT hA OmT kappa & norm_class_all_orders hNT hA OmT Q].
Proof.
have [hU hW hR hP hr] := dgpr_identities_smooth_extensions.
have hI := dgpr_heat_S_inverse_smooth.
split => k.
- exact: (norm_class_scalar_product (hI k) (hW k)).
- exact: (norm_class_scalar_product (hI k) (hP k)).
- have h2 := norm_class_scale 2 (@dgpr_sqrt_time_to_go_class R n T k).
  have hD := norm_class_scalar_product h2 (dgpr_identities_smooth_S k).
  apply: (norm_class_domain_agreement _ (norm_class_scalar_product (hR k)
    (norm_class_compose_on _ hD (scalar_reciprocal_norm_class R k)))).
  all: try by move=> q _.
  move=> [t x] ht; apply: lt0r_neq0.
  change (0 < 2 * Num.sqrt (T - t) * S (t, x)).
  by rewrite !mulr_gt0 ?sqrtr_gt0 ?subr_gt0 // (dgpr_identities_S_pos hS x ht).
- by apply: (norm_class_domain_agreement _ (norm_class_scalar_product (hr k) (hI k))) => q _.
Qed.

(** Source for [dgpr_regularity_log_smooth]: blueprint lem:regularity,
    the class-infinity assertions for log S, log rho and log q on
    Omega_T: S, rho and q are positive there (lem:identities(bounds)),
    and the logarithm is of class infinity on {r : 0 < r}. *)
Theorem dgpr_regularity_log_smooth :
  [/\ norm_class_all_orders hNT hA OmT (fun q => LOG (S q)),
      norm_class_all_orders hNT hA OmT (fun q => LOG (rho q)) &
      norm_class_all_orders hNT hA OmT (fun q => LOG (Q q))].
Proof.
have [_ _ _ _ hr] := dgpr_identities_smooth_extensions.
have [_ _ _ hQ] := dgpr_regularity_smooth.
split => k.
- apply: (norm_class_compose_on _ (dgpr_identities_smooth_S k) (dgpr_logarithm_norm_class R k)).
  by move=> [t x] ht; exact: (dgpr_identities_S_pos hS x ht).
- apply: (norm_class_compose_on _ (hr k) (dgpr_logarithm_norm_class R k)).
  by move=> [t x] ht; exact: (dgpr_identities_rho_pos hS x ht).
- apply: (norm_class_compose_on _ (hQ k) (dgpr_logarithm_norm_class R k)).
  move=> [t x] ht; change (0 < rho (t, x) / S (t, x)).
  by rewrite divr_gt0 // ?(dgpr_identities_rho_pos hS x ht) ?(dgpr_identities_S_pos hS x ht).
Qed.
(** Source for [dgpr_regularity_gaussian_extensions]: blueprint
    lem:regularity, first assertion, for U, W, R, Psi and rho: they have
    Gaussian decay before T (def:classes), by the joint bounds of the
    backward heat extensions (DgprBackwardHeatDecay.v) and
    lem:identities(spt). *)
Theorem dgpr_regularity_gaussian_extensions :
  [/\ dgpr_gaussian_decay_before hA T U, dgpr_gaussian_decay_before hNH T W,
      dgpr_gaussian_decay_before hA T Rr, dgpr_gaussian_decay_before hND T Psi &
      dgpr_gaussian_decay_before hA T rho].
Proof.
have hr : 0 <= r0 := ltW (dgpr_standing_r0 hS).
have hsmu := dgpr_standing_mu_support hS.
have hsups := dgpr_identities_spt hS.
have hsmu0 := dgpr_standing_mu0_support hS.
split.
- exact: (dgpr_backward_heat_gaussian_decay hmu hZ1 hOmu hMmu hsep1 (dgpr_one_measurable hmu)
    (@dgpr_one_bound1 R n) hsmu hr T).
- exact: (dgpr_backward_heat_gaussian_decay hmu hHc hOmu hMmu hHs (dgpr_standing_X_measurable hS)
    (fun y => dgpr_standing_K_norm hS (dgpr_standing_X_values hS y)) hsmu hr T).
- exact: (dgpr_backward_heat_gaussian_decay hups hZ1 hOups hMups hsep1 (dgpr_one_measurable hups)
    (@dgpr_one_bound1 R n) hsups hr T).
- exact: (dgpr_backward_heat_gaussian_decay hups hDc hOups hMups hDs (dgpr_standing_dups_measurable hS)
    (dgpr_standing_dups_bound hS) hsups hr T).
- exact: (dgpr_backward_heat_gaussian_decay hmu0 hZ1 hOmu0 hMmu0 hsep1 (dgpr_one_measurable hmu0)
    (@dgpr_one_bound1 R n) hsmu0 hr T).
Qed.

End HeatObjectsSmooth.
