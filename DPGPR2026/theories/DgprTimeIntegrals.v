(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    dgpr_blueprint.tex, proof of lem:DGPR31: integrals in time. The file
    gives the fundamental theorem of calculus on segments [a,b] with
    b < T for maps of class 1 on R ∩ {t : t < T} (Federer 3.1.11,
    pp. 220-221, and the scalar Lebesgue/Riemann identification of
    2.5.17, p. 111, applied to a continuous extension obtained by the
    retraction of R onto [a,b]); the passage from the segments [0,τ] to
    [0,T) for upper integrals (Lebesgue's increasing convergence theorem,
    Federer 2.4.7, p. 84); and the estimate (eq:31:min) of the integral of
    m(t) = min {γ (T-t)^(-1), δ (T-t)^(-1/2)}. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP RealMetricBackground NormMetric NormClassOneUP
  NormClassZeroTopology NormDifferentialUP NormDifferentialLocal NormHigherCurveDerivativeUP
  NormedCurveFundamentalTheorem NormedStieltjesUP NormedStieltjesLocal NormedStieltjesUnique
  NormedStieltjesLaws StieltjesSubstitution SegmentRetractionTopology StieltjesIntegral
  StieltjesMonotone CurveVariationUP CurveArcLength LebesgueContinuousDegenerateIntegral LebesgueScalarMeasure
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension SummableRealFunctionUP LocalUniquenessExample
  ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealOrderLimit PartialExtendedOrderLoci
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureUpperIntegralMonotone TotalIncreasingIntegralSupremum MeasureIntegralComparison
  RealTotalCharacteristicBounds SummableRealArithmetic NormClassOneLaws
  RealCurveDerivativeUP RealCurveDerivativeAlgebra NormedCurveDerivativeUP SignedSquareRootDerivative
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprParameterIntegralSmooth DgprHeatJetCalculus DgprHeatKernelFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TimeIntegrals.
Variable R : realType.
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_line_before_interior]: R ∩ {t : t < T} is open;
    supporting the proof of lem:DGPR31. *)
Lemma dgpr_line_before_interior (T t : R) : t < T -> norm_domain_interior NR [set s | s < T] t.
Proof.
move=> ht; exists (T - t); split; first by rewrite subr_gt0.
move=> h hh; rewrite /=; have h1 := ler_norm h; lra.
Qed.

(** Source for [dgpr_before_retraction_continuous]: if D is continuous
    on R ∩ {t : t < T} and a <= b < T, then D composed with the
    retraction of R onto [a,b] (Federer 2.5.18(2), p. 112) is continuous
    on R; supporting the proof of lem:DGPR31. *)
Lemma dgpr_before_retraction_continuous (T a b : R) (D : R -> R) :
  a <= b -> b < T -> norm_class_zero NR NR [set t | t < T] D ->
  continuous ((fun x => D (segment_retraction a b x)) : real_line_metric R -> real_line_metric R).
Proof.
move=> hab hbT hD x U hU.
have /andP[_ hup] := segment_retraction_bounds x hab.
have hin : segment_retraction a b x < T := le_lt_trans hup hbT.
have hMap := @norm_class_zero_continuous_at R R^o R^o NR NR hNR hNR [set t | t < T] D _ hD hin.
have hAt := continuous_comp (continuous_comp (@scalar_line_to_norm_continuous R (segment_retraction a b x)) hMap)
  (@scalar_norm_to_line_continuous R (D (segment_retraction a b x))).
exact ((@segment_retraction_continuous R a b x) _ (hAt U hU)).
Qed.

(** Source for [dgpr_before_segment_value]: if D is continuous on
    R ∩ {t : t < T} and a <= b < T, then the integral of D over [a,b]
    with respect to L^1 is the Riemann-Stieltjes integral of the
    retracted map (Federer 2.5.17, p. 111); supporting the proof of
    lem:DGPR31. *)
Lemma dgpr_before_segment_value (T a b : R) (D : R -> R) :
  a <= b -> b < T -> norm_class_zero NR NR [set t | t < T] D ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand D)
    (stieltjes_integral (fun x : R => x) (fun x => D (segment_retraction a b x)) a b)%:E.
Proof.
move=> hab hbT hD.
pose q (x : R) : R := D (segment_retraction a b x).
have hq := dgpr_before_retraction_continuous hab hbT hD.
have hLeb := lebesgue_continuous_segment_integral_including_diagonal hq hab.
apply: measure_integral_graph_equivalent _ hLeb=> x z.
rewrite !partial_function_zero_extension_graph !real_total_integrand_graph.
have hOn : (`[a, b] : set (real_line_metric R)) x -> D (segment_retraction a b x) = D x.
  by rewrite /= in_itv /= => hx; rewrite segment_retraction_id.
split.
- move=> [[hx hz]|[hx hz]].
  + by left; split=> //; rewrite -(hOn hx).
  + by right; split.
- move=> [[hx hz]|[hx hz]].
  + by left; split=> //; rewrite (hOn hx).
  + by right; split.
Qed.

(** Source for [dgpr_before_segment_integrable]: a continuous function
    on R ∩ {t : t < T} has an integral over every segment [a,b] with
    b < T; supporting the proof of lem:DGPR31. *)
Lemma dgpr_before_segment_integrable (T a b : R) (D : R -> R) :
  a <= b -> b < T -> norm_class_zero NR NR [set t | t < T] D ->
  exists G : R, is_measure_subset_integral L1 `[a, b] (real_total_integrand D) G%:E.
Proof. by move=> hab hbT hD; eexists; exact: dgpr_before_segment_value hab hbT hD. Qed.

(** Source for [dgpr_before_ftc_general]: the fundamental theorem of
    calculus, Federer 3.1.11, pp. 220-221, for a map F differentiable on
    R ∩ {t : t < T} with continuous derivative D: the integral of D over
    [a,b], a <= b < T, is F(b) - F(a); supporting the proof of
    lem:DGPR31. *)
Theorem dgpr_before_ftc_general (T a b : R) (F D : R -> R) :
  a <= b -> b < T ->
  (forall t, t < T -> has_norm_differential NR NR [set s | s < T] F t
     (@scalar_coefficient_linear_map R R^o (D t))) ->
  norm_class_zero NR NR [set t | t < T] D ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand D) (F b - F a)%:E.
Proof.
move=> hab hbT hF hD.
have hAB t : a <= t <= b -> [set s | s < T] t.
  by move=> /andP[_ htb]; exact: le_lt_trans htb hbT.
have hFTC := @normed_curve_fundamental_theorem R R^o NR hNR [set s | s < T] F D a b hab hAB
  (fun t ht => hF t ht) hD.
pose q (x : R) : R := D (segment_retraction a b x).
have hq := dgpr_before_retraction_continuous hab hbT hD.
have hEq x : a <= x <= b -> D x = q x by move=> hx; rewrite /q segment_retraction_id.
have hFTCq := @normed_stieltjes_integral_segment_agreement R R^o NR D q (fun x => x) a b
  (F b - F a) hEq hFTC.
have hId : curve_locally_finite_variation ((fun x : R => x) : R -> real_line_metric R).
  by apply: monotone_locally_finite_variation=> x y hxy.
have hRS := normed_stieltjes_scalar_agreement hId hq hab.
have hValue := normed_stieltjes_integral_unique hNR hFTCq hRS.
have hLeb := dgpr_before_segment_value hab hbT hD.
by rewrite -/q -hValue in hLeb.
Qed.

(** Source for [dgpr_line_hom_coefficient]: the linear map [s ↦ s c]
    of R into R has two names; supporting the proof of lem:DGPR31. *)
Lemma dgpr_line_hom_coefficient (c : R) :
  dgpr_line_hom (c : R^o) = @scalar_coefficient_linear_map R R^o c.
Proof. by apply: hom_ext=> s. Qed.

(** Source for [dgpr_before_derivative_class_zero]: the derivative of
    a map of class 1 on R ∩ {t : t < T} (Federer 3.1.1, p. 210) is
    continuous there; supporting the proof of lem:DGPR31. *)
Lemma dgpr_before_derivative_class_zero (T : R) (I DI : R -> R) :
  is_norm_class_one_field NR NR [set t | t < T] I (fun t => dgpr_line_hom (DI t : R^o)) ->
  norm_class_zero NR NR [set t | t < T] DI.
Proof.
move=> hI a ha; split; first exact: dgpr_line_before_interior.
move=> e he; have he2 : 0 < e / 2 by rewrite divr_gt0.
have [d [hd hb]] := norm_class_one_continuity hI ha he2.
exists d; split=> // h hh hd'; have := hb h hh hd' 1.
have e1 : (dgpr_line_hom (DI (a + h) : R^o) - dgpr_line_hom (DI a : R^o)) 1 = DI (a + h) - DI a.
  transitivity (dgpr_line_hom (DI (a + h) : R^o) 1 - dgpr_line_hom (DI a : R^o) 1); first by [].
  by rewrite !dgpr_line_homE !scale1r.
rewrite e1 normr1 mulr1.
by move=> hle; apply: le_lt_trans hle _; rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
Qed.

(** Source for [dgpr_before_ftc]: the fundamental theorem of calculus
    for a map I of class 1 on R ∩ {t : t < T} with derivative
    [s ↦ s DI(t)], in the form produced by lem:classes(cl:dt): the
    integral of DI over [a,b], a <= b < T, is I(b) - I(a); proof of
    lem:DGPR31 (integration over [0,τ]). *)
Theorem dgpr_before_ftc (T a b : R) (I DI : R -> R) :
  a <= b -> b < T ->
  is_norm_class_one_field NR NR [set t | t < T] I (fun t => dgpr_line_hom (DI t : R^o)) ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand DI) (I b - I a)%:E.
Proof.
move=> hab hbT hI.
apply: (dgpr_before_ftc_general hab hbT _ (dgpr_before_derivative_class_zero hI)).
by move=> t ht; rewrite -dgpr_line_hom_coefficient; exact: norm_class_one_differential hI t ht.
Qed.

(** Source for [dgpr_before_upper_integral]: the upper integral over
    [0,T) (Federer 2.4.10, p. 85) of a function phi dominated on [0,T)
    by a nonnegative function g whose integrals over the segments
    [0,τ], 0 <= τ < T, are at most M, is at most M. The proof applies
    Lebesgue's increasing convergence theorem (Federer 2.4.7, p. 84) to
    the restrictions of g to [0, T - T/(k+2)]; proof of lem:DGPR31
    (passage to the limit τ -> T-). *)
Theorem dgpr_before_upper_integral (T M : R) (phi : R -> \bar R) (g : R -> R) :
  0 < T ->
  (forall t, 0 <= t < T -> (phi t <= (g t)%:E)%E) ->
  (forall t, 0 <= t < T -> 0 <= g t) ->
  (forall tau, 0 <= tau < T -> exists G : R,
     is_measure_subset_integral L1 `[0, tau] (real_total_integrand g) G%:E /\ G <= M) ->
  (measure_subset_upper_integral L1 [set t : R | (0 <= t < T)%R]
     (partial_function_total (phi : R -> extended_real_line R)) <= M%:E)%E.
Proof.
move=> hT hphi hg hint.
have hm := lebesgue_scalar_is_measure R.
pose tau (k : nat) : R := T - T / k.+2%:R.
have htau k : 0 <= tau k < T.
  have hk : 0 < k.+2%:R :> R by rewrite ltr0n.
  have hq : 0 < T / k.+2%:R by rewrite divr_gt0.
  have hq2 : T / k.+2%:R <= T.
    by rewrite ler_pdivrMr // ler_peMr ?(ltW hT) // ler1n.
  rewrite /tau; move: hq hq2; set q := T / _ => hq hq2.
  by apply/andP; split; lra.
have htau_mono k l : (k <= l)%N -> tau k <= tau l.
  move=> hkl; rewrite /tau lerD2l lerN2 ler_pM2l // lef_pV2 ?posrE ?ltr0n //.
  by rewrite ler_nat ltnS ltnS.
have [G hG] := choice (fun k => hint (tau k) (htau k)).
pose u (k : nat) (t : R) : extended_real_line R :=
  if (0 <= t) && (t <= tau k) then (g t)%:E else 0%E.
pose w (t : R) : extended_real_line R := if (0 <= t) && (t < T) then (g t)%:E else 0%E.
have hu0 k t : (0 <= u k t)%E.
  rewrite /u; case: ifP=> // /andP[h0 h1]; rewrite lee_fin; apply: hg.
  apply/andP; split=> //; apply: le_lt_trans h1 _; by case/andP: (htau k).
have hlim t : extended_increases_to (fun k => u k t) (w t).
  split.
  - move=> k l hkl; rewrite /u; case: ifP=> [/andP[h0 h1]|_]; last exact: (hu0 l t).
    have -> : (0 <= t) && (t <= tau l) by rewrite h0 /= (le_trans h1 (htau_mono k l hkl)).
    exact: lexx.
  - have [K hK] : exists K, forall k, (K <= k)%N -> u k t = w t.
      rewrite /u /w; case: (boolP ((0 <= t) && (t < T)))=> [/andP[h0 h1]|hn].
      + have hs : 0 < T - t by rewrite subr_gt0.
        have hb := @archi_boundP R (T / (T - t)) (ltW (divr_gt0 hT hs)).
        exists (Num.bound (T / (T - t))) => k hk.
        suff -> : t <= tau k by rewrite h0.
        have hk2 : T / (T - t) <= k.+2%:R.
          by apply: (le_trans (ltW hb)); rewrite ler_nat; apply: (leq_trans hk); rewrite leqW.
        have hkp : 0 < k.+2%:R :> R by rewrite ltr0n.
        rewrite /tau; have : T / k.+2%:R <= T - t.
          by rewrite ler_pdivrMr // mulrC -ler_pdivrMr.
        set q := T / _; lra.
      + exists 0%N => k _; case: ifP=> // /andP[h0 h1].
        exfalso; move: hn; rewrite h0 /= => /negP; apply; apply: le_lt_trans h1 _; by case/andP: (htau k).
    split=> c hc; exists K=> k hk; by rewrite (hK k hk).
have hui k : is_measure_integral L1 (partial_function_total (u k)) (G k)%:E.
  apply: measure_integral_graph_equivalent _ (hG k).1=> x z.
  rewrite partial_function_zero_extension_graph real_total_integrand_graph /=.
  rewrite /u in_itv /=; split.
  - by move=> [[-> <-]|[/negP/negbTE -> ->]].
  - case: ifP=> hx <-; first by left.
    by right; split=> //; rewrite hx.
pose b := extended_real_sup [set c | exists k, c = (G k)%:E].
have hb : is_extended_real_supremum [set c | exists k, c = (G k)%:E] b.
  split; first exact: extended_real_sup_upper.
  exact: extended_real_sup_least.
have hwi := @total_increasing_integral_supremum R R L1 hm u w (fun k => (G k)%:E) b hu0 hlim hui hb.
have hbM : (b <= M%:E)%E.
  by apply: extended_real_sup_least=> c [k ->]; rewrite lee_fin; exact: (hG k).2.
have eb : measure_upper_integral L1 (partial_function_total w) = b.
  exact: (measure_upper_integral_unique (measure_upper_integral_specification _ _) hwi.2.1).
apply: le_trans hbM; rewrite -eb /measure_subset_upper_integral.
apply: measure_upper_integral_monotone=> //.
apply: (@measure_almost_everywhere_mono R R L1 hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
case: (boolP ((0 <= x) && (x < T)))=> hx.
- exists (phi x), (g x)%:E; split; [|split].
  + by apply/partial_function_zero_extension_graph; left.
  + by change (w x = (g x)%:E); rewrite /w hx.
  + exact: hphi.
- exists 0%E, 0%E; split; [|split].
  + apply/partial_function_zero_extension_graph; right; split=> //.
    by move=> hA; move: hx; rewrite /= hA.
  + by change (w x = 0%E); rewrite /w (negbTE hx).
  + exact: lexx.
Qed.

(** Source for [dgpr_segment_integralE]: the integral over [a,b]
    (Federer 2.4.10, p. 85) is the integral of the function equal to g
    on [a,b] and to 0 elsewhere; supporting the proof of lem:DGPR31. *)
Lemma dgpr_segment_integralE (a b : R) (g : R -> R) (G : \bar R) :
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g) G <->
  is_measure_integral L1 (real_total_integrand (fun t => if a <= t <= b then g t else 0)) G.
Proof.
have he x z : partial_function_graph
    (partial_function_zero_extension (0 : extended_real_line R) `[a, b] (real_total_integrand g)) x z <->
    partial_function_graph (real_total_integrand (fun t => if a <= t <= b then g t else 0)) x z.
  rewrite partial_function_zero_extension_graph !real_total_integrand_graph /= in_itv /=.
  case: ifP=> hx; split.
  - by move=> [[_ ->]|[hn _]].
  - by move=> <-; left.
  - by move=> [[hp _]|[_ ->]].
  - by move=> <-; right; split=> //; rewrite hx.
split=> h.
- exact: (measure_integral_graph_equivalent he h).
- by apply: (measure_integral_graph_equivalent _ h)=> x z; rewrite he.
Qed.

(** Source for [dgpr_segment_integral_add]: additivity of the integral
    over [a,b] (Federer 2.4.4, p. 82); supporting the proof of
    lem:DGPR31. *)
Lemma dgpr_segment_integral_add (a b G1 G2 : R) (g1 g2 : R -> R) :
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g1) G1%:E ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g2) G2%:E ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand (fun t => g1 t + g2 t)) (G1 + G2)%:E.
Proof.
move=> /dgpr_segment_integralE h1 /dgpr_segment_integralE h2; apply/dgpr_segment_integralE.
have h := real_total_integral_add (lebesgue_scalar_is_measure R) h1 h2.
have -> : (fun t => if a <= t <= b then g1 t + g2 t else 0) =
    (fun t => (if a <= t <= b then g1 t else 0) + (if a <= t <= b then g2 t else 0)).
  by apply: funext=> t; case: ifP; rewrite ?addr0.
exact: h.
Qed.

(** Source for [dgpr_segment_integral_scale]: homogeneity of the
    integral over [a,b] (Federer 2.4.4, p. 82); supporting the proof
    of lem:DGPR31. *)
Lemma dgpr_segment_integral_scale (a b c G : R) (g : R -> R) :
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g) G%:E ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand (fun t => c * g t)) (c * G)%:E.
Proof.
move=> /dgpr_segment_integralE h1; apply/dgpr_segment_integralE.
have h := real_total_integral_scale (lebesgue_scalar_is_measure R) c h1.
have -> : (fun t => if a <= t <= b then c * g t else 0) =
    (fun t => c * (if a <= t <= b then g t else 0)).
  by apply: funext=> t; case: ifP; rewrite ?mulr0.
exact: h.
Qed.

(** Source for [dgpr_segment_integral_le]: monotonicity of the
    integral over [a,b] (Federer 2.4.4, p. 82); supporting the proof
    of lem:DGPR31. *)
Lemma dgpr_segment_integral_le (a b G1 G2 : R) (g1 g2 : R -> R) :
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g1) G1%:E ->
  is_measure_subset_integral L1 `[a, b] (real_total_integrand g2) G2%:E ->
  (forall t, a <= t <= b -> g1 t <= g2 t) -> G1 <= G2.
Proof.
move=> /dgpr_segment_integralE h1 /dgpr_segment_integralE h2 hle.
have hm := lebesgue_scalar_is_measure R.
suff : (G1%:E <= G2%:E)%E by rewrite lee_fin.
apply: (measure_integral_monotone hm h1 h2).
apply: real_total_pointwise_order_almost=> // t.
by case: ifP=> ht //; exact: hle.
Qed.

(** Source for [dgpr_before_curve_differential]: a derivative of a
    real function of one variable at t < T gives its differential at t
    relative to R ∩ {s : s < T} (Federer 3.1.1, p. 209); supporting the
    proof of lem:DGPR31. *)
Lemma dgpr_before_curve_differential (T t : R) (F : R -> R) (v : R) : t < T ->
  has_real_curve_derivative F t v ->
  has_norm_differential NR NR [set s | s < T] F t (@scalar_coefficient_linear_map R R^o v).
Proof.
move=> ht hF.
apply: (norm_differential_restrict (A := setT) (fun y _ => Logic.I) (dgpr_line_before_interior ht)).
exact: (dgpr_curve_to_differential hNR ((scalar_normed_curve_derivative F t v).2 hF)).
Qed.

(** Source for [dgpr_before_curve_class_zero]: a real function of one
    variable differentiable at every t < T is continuous on
    R ∩ {t : t < T} (Federer 3.1.1, p. 209); supporting the proof of
    lem:DGPR31. *)
Lemma dgpr_before_curve_class_zero (T : R) (F : R -> R) :
  (forall t, t < T -> exists v, has_real_curve_derivative F t v) ->
  norm_class_zero NR NR [set t | t < T] F.
Proof.
move=> h a ha; have [v hv] := h a ha.
have hd := dgpr_before_curve_differential ha hv.
split; first exact: (norm_differential_interior hd).
by move=> e he; exact: (norm_differential_continuous_at hNR hd he).
Qed.

(** Source for [dgpr_min_difference]: |min(a,b) - min(c,d)| is at
    most |a - c| + |b - d|; supporting the proof of lem:DGPR31. *)
Lemma dgpr_min_difference (a b c d : R) :
  `|Num.min a b - Num.min c d| <= `|a - c| + `|b - d|.
Proof.
have h1 := ler_norm (a - c); have h2 := ler_norm (c - a); rewrite distrC in h2.
have h3 := ler_norm (b - d); have h4 := ler_norm (d - b); rewrite distrC in h4.
rewrite ler_norml /Num.min; case: (ltP a b)=> hab; case: (ltP c d)=> hcd;
  by apply/andP; split; lra.
Qed.

(** Source for [dgpr_class_zero_min]: the minimum of two functions
    continuous on R ∩ {t : t < T} is continuous there; supporting the
    proof of lem:DGPR31. *)
Lemma dgpr_class_zero_min (T : R) (f1 f2 : R -> R) :
  norm_class_zero NR NR [set t | t < T] f1 -> norm_class_zero NR NR [set t | t < T] f2 ->
  norm_class_zero NR NR [set t | t < T] (fun t => Num.min (f1 t) (f2 t)).
Proof.
move=> h1 h2 a ha; split; first exact: (h1 a ha).1.
move=> e he; have he2 : 0 < e / 2 by rewrite divr_gt0.
have [d1 [hd1 hb1]] := (h1 a ha).2 _ he2.
have [d2 [hd2 hb2]] := (h2 a ha).2 _ he2.
exists (Num.min d1 d2); split; first by rewrite lt_min hd1 hd2.
move=> h hA hh; rewrite lt_min in hh; case/andP: hh=> hh1 hh2.
apply: le_lt_trans (dgpr_min_difference _ _ _ _) _.
have := hb1 h hA hh1; have := hb2 h hA hh2; lra.
Qed.

(** Source for [dgpr_sqrt_time_derivative]: the derivative of
    [r ↦ (T - r)^(1/2)] at t < T is -(2 (T - t)^(1/2))^(-1);
    supporting the proof of lem:DGPR31. *)
Lemma dgpr_sqrt_time_derivative (T t : R) : t < T ->
  has_real_curve_derivative (fun r => Num.sqrt (T - r)) t (- (2 * Num.sqrt (T - t))^-1).
Proof.
move=> ht; have hs : 0 < T + t * -1 by rewrite mulrN1 subr_gt0.
have h1 := dgpr_real_curve_affine T (-1) t.
have h : has_real_curve_derivative (fun r => Num.sqrt (T + r * -1)) t
    ((2 * Num.sqrt (T + t * -1))^-1 * -1).
  exact: (dgpr_real_curve_chain h1 (positive_square_root_real_derivative hs)).
have e : (fun r => Num.sqrt (T + r * -1)) = (fun r => Num.sqrt (T - r)).
  by apply: funext => r; rewrite mulrN1.
by move: h; rewrite e !mulrN1.
Qed.

(** Source for [dgpr_time_reciprocal_derivative]: the derivative of
    [r ↦ c (T - r)^(-1)] at t < T exists; supporting the proof of
    lem:DGPR31. *)
Lemma dgpr_time_reciprocal_derivative (T c t : R) : t < T ->
  exists v, has_real_curve_derivative (fun r => c / (T - r)) t v.
Proof.
move=> ht; have hs : T + t * -1 != 0 by rewrite mulrN1 subr_eq0 gt_eqF.
have h1 := dgpr_real_curve_affine T (-1) t.
have h2 := dgpr_real_curve_chain h1 (dgpr_real_curve_reciprocal hs).
have h3 := dgpr_real_curve_product (dgpr_real_curve_constant c t) h2.
have e : (fun r => c * (T + r * -1)^-1) = (fun r => c / (T - r)).
  by apply: funext => r; rewrite mulrN1.
by rewrite e in h3; eexists; exact: h3.
Qed.

(** Source for [dgpr_time_inverse_root_derivative]: the derivative of
    [r ↦ c (T - r)^(-1/2)] at t < T exists; supporting the proof of
    lem:DGPR31. *)
Lemma dgpr_time_inverse_root_derivative (T c t : R) : t < T ->
  exists v, has_real_curve_derivative (fun r => c / Num.sqrt (T - r)) t v.
Proof.
move=> ht; have hs : Num.sqrt (T - t) != 0 by rewrite gt_eqF // sqrtr_gt0 subr_gt0.
have h2 := dgpr_real_curve_chain (dgpr_sqrt_time_derivative ht) (dgpr_real_curve_reciprocal hs).
have h3 := dgpr_real_curve_product (dgpr_real_curve_constant c t) h2.
by eexists; exact: h3.
Qed.

(** Source for [dgpr_time_min_class_zero]: the function
    m(t) = min {γ (T-t)^(-1), δ (T-t)^(-1/2)} of (eq:31:eta) is
    continuous on R ∩ {t : t < T}; proof of lem:DGPR31. *)
Lemma dgpr_time_min_class_zero (T gamma delta : R) :
  norm_class_zero NR NR [set t | t < T]
    (fun t => Num.min (gamma / (T - t)) (delta / Num.sqrt (T - t))).
Proof.
apply: dgpr_class_zero_min; apply: dgpr_before_curve_class_zero=> t ht.
- exact: dgpr_time_reciprocal_derivative.
- exact: dgpr_time_inverse_root_derivative.
Qed.

(** Source for [dgpr_time_min_nonnegative]: m(t) >= 0 for t < T;
    proof of lem:DGPR31. *)
Lemma dgpr_time_min_nonnegative (T gamma delta t : R) : 0 <= gamma -> 0 <= delta -> t < T ->
  0 <= Num.min (gamma / (T - t)) (delta / Num.sqrt (T - t)).
Proof.
move=> hg hd ht; have hs : 0 < T - t by rewrite subr_gt0.
by rewrite le_min !divr_ge0 ?(ltW hs) ?sqrtr_ge0.
Qed.

(** Source for [dgpr_min_primitive_derivative]: for c > 0 the
    derivative of H(r) = -4 γ log((T - r)^(1/2) + c) at t < T is
    h(t) = 2 γ ((T - t)^(1/2) ((T - t)^(1/2) + c))^(-1); proof of
    lem:DGPR31, (eq:31:min). *)
Lemma dgpr_min_primitive_derivative (T c gamma t : R) : 0 < c -> t < T ->
  has_real_curve_derivative (fun r => - (4 * gamma) * LOG (Num.sqrt (T - r) + c)) t
    (2 * gamma / (Num.sqrt (T - t) * (Num.sqrt (T - t) + c))).
Proof.
move=> hc ht; have hu : 0 < Num.sqrt (T - t) by rewrite sqrtr_gt0 subr_gt0.
have huc : 0 < Num.sqrt (T - t) + c by rewrite addr_gt0.
have hv := dgpr_real_curve_add (dgpr_sqrt_time_derivative ht) (dgpr_real_curve_constant c t).
have [hl _] := @dgpr_real_curve_logarithm R.
have h2 := dgpr_real_curve_chain hv (hl _ huc).
have h3 := dgpr_real_curve_product (dgpr_real_curve_constant (- (4 * gamma)) t) h2.
have e (g u c' : R) : u != 0 -> u + c' != 0 ->
    0 * LOG (u + c') + - (4 * g) * ((u + c')^-1 * (- (2 * u)^-1 + 0)) = 2 * g / (u * (u + c')).
  by move=> hu0 huc0; rewrite mul0r add0r; field; rewrite ?hu0 ?huc0.
by rewrite e ?gt_eqF // in h3.
Qed.

(** Source for [dgpr_min_majorant_class_zero]: the function h of
    [dgpr_min_primitive_derivative] is continuous on
    R ∩ {t : t < T}; proof of lem:DGPR31, (eq:31:min). *)
Lemma dgpr_min_majorant_class_zero (T c gamma : R) : 0 < c ->
  norm_class_zero NR NR [set t | t < T]
    (fun t => 2 * gamma / (Num.sqrt (T - t) * (Num.sqrt (T - t) + c))).
Proof.
move=> hc; apply: dgpr_before_curve_class_zero=> t ht.
have hu : 0 < Num.sqrt (T - t) by rewrite sqrtr_gt0 subr_gt0.
have huc : 0 < Num.sqrt (T - t) + c by rewrite addr_gt0.
have hs := dgpr_sqrt_time_derivative ht.
have hv := dgpr_real_curve_add hs (dgpr_real_curve_constant c t).
have hw := dgpr_real_curve_product hs hv.
have hw0 : Num.sqrt (T - t) * (Num.sqrt (T - t) + c) != 0 by rewrite gt_eqF // mulr_gt0.
have h2 := dgpr_real_curve_chain hw (dgpr_real_curve_reciprocal hw0).
have h3 := dgpr_real_curve_product (dgpr_real_curve_constant (2 * gamma) t) h2.
by eexists; exact: h3.
Qed.

(** Source for [dgpr_min_majorant]: m(t) <= h(t) for t < T, where
    c = γ/δ; proof of lem:DGPR31, (eq:31:min). The two cases
    (T - t)^(1/2) >= c and (T - t)^(1/2) <= c correspond to the two
    cases of the blueprint. *)
Lemma dgpr_min_majorant (T gamma delta t : R) : 0 < gamma -> 0 < delta -> t < T ->
  Num.min (gamma / (T - t)) (delta / Num.sqrt (T - t)) <=
    2 * gamma / (Num.sqrt (T - t) * (Num.sqrt (T - t) + gamma / delta)).
Proof.
move=> hg hd ht; have hs : 0 <= T - t by rewrite subr_ge0 ltW.
pose u := Num.sqrt (T - t); pose c := gamma / delta.
have hu : 0 < u by rewrite sqrtr_gt0 subr_gt0.
have hc : 0 < c by rewrite divr_gt0.
have huc : 0 < u + c by rewrite addr_gt0.
have eT : T - t = u ^+ 2 by rewrite sqr_sqrtr.
have eg : gamma = c * delta by rewrite /c divfK ?gt_eqF.
rewrite -/u -/c [X in gamma / X]eT ge_min; case: (leP c u)=> hcu; apply/orP; [left|right].
- rewrite -subr_ge0.
  have e (g u' c' : R) : u' != 0 -> u' + c' != 0 ->
      2 * g / (u' * (u' + c')) - g / (u' ^+ 2) = g * (u' - c') / (u' ^+ 2 * (u' + c')).
    by move=> hu0 huc0; field; rewrite ?hu0 ?huc0.
  rewrite e ?gt_eqF //; apply: divr_ge0; first by apply: mulr_ge0; [exact: ltW|rewrite subr_ge0].
  by apply: mulr_ge0; [exact: sqr_ge0|exact: ltW].
- rewrite -subr_ge0 [X in 2 * X]eg.
  have e (d u' c' : R) : u' != 0 -> u' + c' != 0 ->
      2 * (c' * d) / (u' * (u' + c')) - d / u' = d * (c' - u') / (u' * (u' + c')).
    by move=> hu0 huc0; field; rewrite ?hu0 ?huc0.
  rewrite e ?gt_eqF //; apply: divr_ge0; first by apply: mulr_ge0; [exact: ltW|rewrite subr_ge0 ltW].
  by apply: mulr_ge0; exact: ltW.
Qed.

(** Source for [dgpr_time_min_integral]: (eq:31:min) of the proof of
    lem:DGPR31: for 0 <= τ < T the integral of
    m(t) = min {γ (T-t)^(-1), δ (T-t)^(-1/2)} over [0,τ] is at most
    4 γ log(1 + T^(1/2) δ / γ). The proof differs from the blueprint:
    instead of the two cases T^(1/2) δ / γ <= 1 and > 1 it uses the
    single majorant h(t) = 2 γ ((T-t)^(1/2) ((T-t)^(1/2) + γ/δ))^(-1)
    with primitive -4 γ log((T-t)^(1/2) + γ/δ). *)
Theorem dgpr_time_min_integral (T gamma delta tau : R) :
  0 < T -> 0 < gamma -> 0 <= delta -> 0 <= tau < T ->
  exists G : R, is_measure_subset_integral L1 `[0, tau]
      (real_total_integrand (fun t => Num.min (gamma / (T - t)) (delta / Num.sqrt (T - t)))) G%:E /\
    G <= 4 * gamma * LOG (1 + Num.sqrt T * delta / gamma).
Proof.
move=> hT hg hd /andP[h0 htT].
have [G hG] := dgpr_before_segment_integrable h0 htT (@dgpr_time_min_class_zero T gamma delta).
exists G; split=> //.
move: hd; rewrite le_eqVlt=> /orP[/eqP hd0|hdp].
- rewrite -hd0 mulr0 mul0r addr0 real_logarithm_one mulr0.
  have hF t : t < T -> has_norm_differential NR NR [set s | s < T] (fun _ => 0) t
      (@scalar_coefficient_linear_map R R^o 0).
    by move=> ht; exact: dgpr_before_curve_differential ht (dgpr_real_curve_constant 0 t).
  have hZ : norm_class_zero NR NR [set t | t < T] (fun _ : R => 0 : R).
    by apply: dgpr_before_curve_class_zero=> t _; exists 0; exact: dgpr_real_curve_constant.
  have hI := dgpr_before_ftc_general h0 htT hF hZ; rewrite subr0 in hI.
  apply: (dgpr_segment_integral_le hG hI)=> t /andP[_ ht].
  have hs : 0 < T - t by rewrite subr_gt0 (le_lt_trans ht htT).
  by rewrite ge_min -hd0 mul0r lexx orbT.
- pose c := gamma / delta.
  have hc : 0 < c by rewrite divr_gt0.
  pose H r := - (4 * gamma) * LOG (Num.sqrt (T - r) + c).
  have hF t : t < T -> has_norm_differential NR NR [set s | s < T] H t
      (@scalar_coefficient_linear_map R R^o
        (2 * gamma / (Num.sqrt (T - t) * (Num.sqrt (T - t) + c)))).
    by move=> ht; exact: dgpr_before_curve_differential ht (dgpr_min_primitive_derivative gamma hc ht).
  have hI := dgpr_before_ftc_general h0 htT hF (dgpr_min_majorant_class_zero gamma hc).
  apply: le_trans (dgpr_segment_integral_le hG hI _) _.
    move=> t /andP[_ ht]; exact: dgpr_min_majorant hg hdp (le_lt_trans ht htT).
  have hsT : 0 < Num.sqrt T by rewrite sqrtr_gt0.
  have hsr : 0 <= Num.sqrt (T - tau) by rewrite sqrtr_ge0.
  have eH : H tau - H 0 = 4 * gamma * (LOG (Num.sqrt T + c) - LOG (Num.sqrt (T - tau) + c)).
    by rewrite /H subr0; ring.
  rewrite eH.
  have hlog : LOG (Num.sqrt T + c) - LOG (Num.sqrt (T - tau) + c) <=
      LOG (1 + Num.sqrt T * delta / gamma).
    have e : 1 + Num.sqrt T * delta / gamma = (Num.sqrt T + c) / c.
      by rewrite /c mulrDl divff ?gt_eqF // addrC invf_div mulrA.
    have hc2 : 0 < Num.sqrt (T - tau) + c by rewrite ltr_wpDl.
    rewrite e real_logarithm_ratio ?addr_gt0 // lerD2l lerN2.
    have hcc : c <= Num.sqrt (T - tau) + c by rewrite lerDr.
    by rewrite real_logarithm_order.
  by rewrite ler_pM2l ?mulr_gt0.
Qed.

End TimeIntegrals.
