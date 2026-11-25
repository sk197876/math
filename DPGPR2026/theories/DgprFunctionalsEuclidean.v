(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    mr:functionals, first consequence, for distributions on R^n: if ν is a
    Radon measure over R^n and S is a distribution on R^n with values in
    a normed space Y with a finite basis such that
    S(φ) ≤ ∫^* |φ| dν for every test function φ (Federer 2.4.2), then S
    is representable by integration (Federer 4.1.5) and its variation
    measure ‖S‖ satisfies ‖S‖(A) ≤ ν(A) for every A ⊆ R^n. Federer's
    variation measure lives on the current domain of R^n, the set type of
    the whole space with the topology of the Euclidean norm; ν is
    transported to it by the homeomorphism
    [euclidean_full_domain_point], and the conclusion is stated as
    ‖S‖(A) ≤ ν({x : x ∈ A}) for subsets A of the current domain. The
    abstract inequality is [dgpr_variation_dominated] of DgprFunctionals
    (Federer 2.5.14). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm InnerMetric
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentDomainGeometry
  IsotropyGroupTopology SubtypeCompactHausdorff ProperMapUP RadonProperPushforward
  EuclideanDistributionMeasureContext EuclideanFullDomainMeasure MeasureUP MeasurePushforward
  RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  InjectivePushforwardIntegral PartialFunctionUP PartialFunctionBasic
  SummableRealFunctionUP FunctionLatticeUP CompactSupportFunctionUP ContinuousDualUP
  WeakEvaluationTopologyUP SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationDomain DistributionVariationUP DistributionVariationSealed
  DistributionFiniteVariationUP NormalisedDistributionRepresentationUP
  DistributionIntegrationRepresentationUP RadonCompactScalarIntegral MeasureIntegralBounds
  MeasureUpperIntegralMonotone RealTotalCharacteristicBounds ExtendedRealBoundsUP ExtendedRealBounds
  ExtendedSupremumUP LinearBasis.
From DPGPR Require Import DgprFunctionals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FullDomain.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation IT := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation FT := (current_domain R n (fun _ => True)).
Local Notation p := (@euclidean_full_domain_point R n).
Local Notation hFull := (fun (x : X) (_ : True) => @norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).

Variable nu : set IT -> \bar R.
Hypothesis hn : is_measure nu.
Hypothesis hnr : is_radon_measure nu.

(** Source for [dgpr_full_domain_measure_laws]: blueprint
    mr:functionals; supporting lemma. The image of the Radon measure ν
    over R^n under the homeomorphism of R^n onto its current domain is a
    Radon measure (Federer 2.2.17), as in [euclidean_full_domain_measure_laws]. *)
Lemma dgpr_full_domain_measure_laws :
  is_measure (measure_pushforward p nu) /\ is_radon_measure (measure_pushforward p nu).
Proof.
have hForward : continuous (fun x : IT => p x).
  apply: (@set_type_continuous_into NT (fun _ => True) IT p).
  exact: (@euclidean_distribution_inner_to_norm R n).
have hInverse : continuous (fun x : FT => (set_val x : IT)).
  move=> x; exact: (continuous_comp (@set_type_val_continuous NT (fun _ => True) x)
    (@euclidean_distribution_norm_to_inner R n (set_val x))).
have hProper : @is_proper_map IT FT p.
  move=> K hK.
  have hCompact : compact ((fun x : FT => (set_val x : IT)) @` K).
    apply: continuous_compact hK; exact: continuous_subspaceT hInverse.
  have hEqual : ((fun x : FT => (set_val x : IT)) @` K) = p @^-1` K.
    apply/seteqP; split.
    - move=> x [y hy hyx].
      have hSame : p x = y by apply: val_inj; exact: esym hyx.
      exact (eq_ind y K hy _ (esym hSame)).
    - move=> x hx; exists (p x); by [].
  by rewrite -hEqual.
have hHausdorff : hausdorff_space FT.
  exact: (@set_type_hausdorff NT (fun _ => True) (@metric_hausdorff R NT)).
split; first exact: measure_pushforward_is_measure hn.
exact: (@proper_continuous_radon_pushforward R IT FT nu hn hnr p hHausdorff
  (@current_domain_locally_compact R n (fun _ => True) hFull) hForward hProper).
Qed.

(** Source for [dgpr_full_domain_integral]: blueprint mr:functionals;
    supporting lemma. An integral of f with respect to the image measure
    is an integral of f composed with the identification with respect to
    ν (Federer 2.4.18(1), for an injective map). *)
Lemma dgpr_full_domain_integral (f : FT -> R) (b : \bar R) :
  is_measure_integral (measure_pushforward p nu) (real_total_integrand f) b ->
  is_measure_integral nu (real_total_integrand (fun x : IT => f (p x))) b.
Proof.
have hInj : injective p by move=> x y h; exact: (congr1 set_val h).
move=> hI; have h := (@injective_pushforward_integral_iff R IT FT nu hn p
  (real_total_integrand f) hInj b).2 hI.
apply: (measure_integral_graph_equivalent _ h) => x z.
change (partial_function_graph (real_total_integrand f) (p x) z <->
  partial_function_graph (real_total_integrand (fun x : IT => f (p x))) x z).
by rewrite !real_total_integrand_graph.
Qed.

(** Source for [dgpr_full_domain_preimage]: blueprint mr:functionals;
    supporting lemma. The inverse image of A under the identification is
    the set of the points of R^n underlying A. *)
Lemma dgpr_full_domain_preimage (A : set FT) : p @^-1` A = set_val @` A.
Proof.
apply/seteqP; split.
- move=> x hx; exists (p x) => //.
- move=> x [y hy <-]; rewrite /preimage /=.
  have -> : p (set_val y) = y by apply: val_inj.
  exact: hy.
Qed.

End FullDomain.

Section DominatedFunctional.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NT := (real_norm_metric_space hN).
Local Notation IT := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation FT := (current_domain R n setT).
Local Notation p := (@euclidean_full_domain_point R n).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable S : Hom (smooth_test_space hE) R^o.
Variable nu : set IT -> \bar R.
Hypothesis hn : is_measure nu.
Hypothesis hnr : is_radon_measure nu.
Hypothesis hS : forall phi, ((S phi)%:E <=
  measure_upper_integral nu (real_total_integrand (fun x => NY (smooth_test_value hE phi x))))%E.
Local Notation value := (@distribution_domain_values R NT setT Y (smooth_test_space hE)
  (smooth_test_values_hom hE)).
Local Notation nuF := (measure_pushforward p nu).

(** Source for [dgpr_dominated_gauge_bound]: blueprint mr:functionals,
    first consequence: if |φ(x)| ≤ f(x) for x ∈ R^n and b is the integral
    of f with respect to the image of ν, then S(φ) ≤ ∫^* |φ| dν ≤ b by
    the monotonicity of the upper integral (Federer 2.4.2, 2.4.4). *)
Lemma dgpr_dominated_gauge_bound (f : FT -> R) (b : R) phi :
  is_measure_integral nuF (real_total_integrand f) b%:E ->
  (forall x, NY (value phi x) <= f x) -> S phi <= b.
Proof.
move=> hI hphi.
have hJ := dgpr_full_domain_integral hn hI.
have hpt : forall x : IT, NY (smooth_test_value hE phi x) <= f (p x).
  move=> x; exact: (hphi (p x)).
have hmono := measure_upper_integral_monotone hn (real_total_pointwise_order_almost hn hpt).
have hb : measure_upper_integral nu (real_total_integrand (fun x : IT => f (p x))) = b%:E.
  exact: measure_upper_integral_unique (measure_upper_integral_specification nu _) hJ.2.1.
by rewrite -lee_fin; apply: le_trans (hS phi) _; rewrite -hb.
Qed.

(** Source for [dgpr_dominated_finite_variation]: blueprint
    mr:functionals, first consequence: S is representable by
    integration, since ‖S‖(f) ≤ ∫ f dν < ∞ for f ∈ K(R^n)^+ (Federer
    4.1.5 and 2.5.14). *)
Theorem dgpr_dominated_finite_variation :
  @is_finite_distribution_variation R NT setT Y NY (smooth_test_space hE)
    (smooth_test_values_hom hE) S.
Proof.
apply: (proj2 (@finite_distribution_variation_gauge_iff R NT setT Y NY hNY
  (smooth_test_space hE) (smooth_test_values_hom hE) S)) => f hf.
have [hm hr] := dgpr_full_domain_measure_laws hn hnr.
have hint := radon_positive_compact_integral_laws hm hr hf.
have hgauge := @DistributionVariation.laws R FT Y NY hNY (smooth_test_space hE) value S f hf.2.
apply: le_lt_trans (ltry (radon_positive_compact_integral hm hr f)).
apply: (extended_supremum_least hgauge) => a [phi [hphi <-]].
rewrite lee_fin; exact: dgpr_dominated_gauge_bound hint hphi.
Qed.

(** Source for [dgpr_dominated_variation]: blueprint mr:functionals,
    first consequence: ‖S‖(A) ≤ ν(A) for every A ⊆ R^n, because
    ‖S‖(f) ≤ ∫ f dν for f ∈ K(R^n)^+ and both measures are Radon
    measures (Federer 2.5.14); ‖S‖ is any variation measure of S in the
    sense of Federer 4.1.5. *)
Theorem dgpr_dominated_variation (D : lmodType R) (ed : Hom D (Hom Y R^o)) (DN : D -> R)
    (hD : is_continuous_dual hNY ed DN) (O : set (set D))
    (hO : is_weak_evaluation_topology (fun a y => ed a y) O)
    (rho : set FT -> \bar R) (k : FT -> D) :
  is_normalised_distribution_representation hD hO value S rho k ->
  forall A, (rho A <= nu (set_val @` A))%E.
Proof.
move=> hrep A; have hlaws := normalised_distribution_representation_laws hrep.
have [hm hr] := dgpr_full_domain_measure_laws hn hnr.
have hU : forall x : X, setT x -> norm_domain_interior N setT x.
  move=> x _; exact: norm_full_domain_interior.
have h := @dgpr_variation_dominated R FT Y NY (smooth_test_space hE) value S rho
  (distribution_representation_measure hlaws) (distribution_representation_radon hlaws)
  (current_domain_locally_compact hU) (normalised_distribution_original_gauge hrep) nuF hm hr
  (fun f _ b hb phi hphi => dgpr_dominated_gauge_bound hb hphi) A.
by rewrite /measure_pushforward dgpr_full_domain_preimage in h.
Qed.

(** Source for [dgpr_dominated_representation]: blueprint
    mr:functionals, first consequence, combined with the representation
    of [dgpr_functional_representation]: S has a variation measure ‖S‖
    and a normalised density (Federer 4.1.5), and ‖S‖(A) ≤ ν(A) for
    every A ⊆ R^n. *)
Theorem dgpr_dominated_representation d (bY : 'I_d -> Y) (hbY : is_basis bY)
    (D : lmodType R) (ed : Hom D (Hom Y R^o)) (DN : D -> R)
    (hD : is_continuous_dual hNY ed DN) (O : set (set D))
    (hO : is_weak_evaluation_topology (fun a y => ed a y) O) :
  exists rho : set FT -> \bar R, exists k : FT -> D,
    is_normalised_distribution_representation hD hO value S rho k /\
    forall A, (rho A <= nu (set_val @` A))%E.
Proof.
have hU : forall x : X, setT x -> norm_domain_interior N setT x.
  move=> x _; exact: norm_full_domain_interior.
have [rho [k hrep]] := @dgpr_functional_representation R n Y NY hNY d bY hbY setT hU E ev hE S
  D ed DN hD O hO dgpr_dominated_finite_variation.
exists rho, k; split=> //; exact: dgpr_dominated_variation hrep.
Qed.

End DominatedFunctional.
