(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:classes(cl:div): if g : R^n -> R^n is differentiable
    and |g(x)| + ‖Dg(x)‖ <= c exp(-|x|^2/c) for x in R^n, then
    ∫ div g dL^n = 0; if f : R^n -> R has Gaussian decay, then
    ∫ Delta f dL^n = 0. The proof differs from the blueprint, which uses
    Fubini's theorem: here the difference quotients of each coordinate of
    g have integral 0 by the translation invariance of L^n (Federer 2.7.16,
    p. 135), and Lebesgue's bounded convergence theorem (2.4.9, p. 85)
    passes to the limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP RealMetricBackground GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric HilbertFormCompactness InnerConvex
  NormDifferentialUP NormDifferentialLocal NormDifferentialConvexBound NormClassOneUP
  PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasureIntegralUP NormClassZeroTotalMeasurable
  SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderLimit RealErrorOrderLimit
  RealDominatedIntegralLimit EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  RealExponentialUP RealExponentialSealed RealExponentialLaws LatticeL1ApproximationLaws
  FiniteCoordinates LinearBasis FiniteDualDimension TraceDefinition EuclideanCoordinateMetric
  EuclideanTraceContinuity ProductInnerDifferential ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm ContinuousMultilinearEvaluationBound NormHigherDifferentialUP
  MultilinearArguments MultilinearSuccessorArguments.
From DPGPR Require Import DgprGrowthClasses.
From DPGPR Require Import DgprLebesgueIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Directional.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).
Local Notation NR := (fun t : R^o => `|t|).
Local Notation hNR := (@scalar_absolute_value_norm R).

(** Source for [dgpr_differentiable_continuous]: Federer 3.1.1,
    pp. 209-210: a function differentiable at every point of R^n is
    continuous. *)
Lemma dgpr_differentiable_continuous (phi : X -> R) (Dphi : X -> Hom X R^o) :
  (forall x, has_norm_differential NX NR setT phi x (Dphi x)) ->
  forall a e, 0 < e -> exists d, 0 < d /\ forall h, NX h < d -> `|phi (a + h) - phi a| < e.
Proof.
move=> hd a e he.
have [d [hd0 h]] := @norm_differential_continuous_at R X R^o NX NR hNR setT phi a (Dphi a) (hd a) e he.
by exists d; split=> // h0 hh; exact: h h0 Logic.I hh.
Qed.

(** Source for [dgpr_continuous_class_zero]: Federer 3.1.1, p. 210:
    the epsilon form of continuity at every point of R^n gives class 0. *)
Lemma dgpr_continuous_class_zero (phi : X -> R) :
  (forall a e, 0 < e -> exists d, 0 < d /\ forall h, NX h < d -> `|phi (a + h) - phi a| < e) ->
  norm_class_zero NX NR setT phi.
Proof.
move=> hc a _; split; first by exists 1; split=> // h _.
move=> e he; have [d [hd h]] := hc a e he.
by exists d; split=> // h0 _ hh; exact: h.
Qed.

(** Source for [dgpr_quotient_class_zero]: Federer 3.1.1, p. 210:
    the difference quotient [x ↦ s (phi (x + w) - phi x)] of a continuous
    function phi is continuous. *)
Lemma dgpr_quotient_class_zero (phi : X -> R) (s : R) (w : X) :
  (forall a e, 0 < e -> exists d, 0 < d /\ forall h, NX h < d -> `|phi (a + h) - phi a| < e) ->
  norm_class_zero NX NR setT (fun x => s * (phi (x + w) - phi x)).
Proof.
move=> hc; apply: dgpr_continuous_class_zero=> a e he.
have hT : 0 < `|s| + 1 by have := normr_ge0 s; lra.
pose e' := e / (2 * (`|s| + 1)).
have he' : 0 < e' by rewrite /e' divr_gt0 //; lra.
have [d1 [hd1 h1]] := hc (a + w) e' he'.
have [d2 [hd2 h2]] := hc a e' he'.
exists (Num.min d1 d2); split; first by rewrite lt_min hd1 hd2.
move=> h hh.
have hh1 : NX h < d1 by apply: lt_le_trans hh _; rewrite ge_min lexx.
have hh2 : NX h < d2 by apply: lt_le_trans hh _; rewrite ge_min lexx orbT.
have -> : s * (phi (a + h + w) - phi (a + h)) - s * (phi (a + w) - phi a) =
    s * ((phi (a + w + h) - phi (a + w)) - (phi (a + h) - phi a)).
  by rewrite (addrAC a h w); ring.
have hA := h1 h hh1; have hB := h2 h hh2.
rewrite normrM.
have hsum : `|(phi (a + w + h) - phi (a + w)) - (phi (a + h) - phi a)| <= 2 * e'.
  apply: le_trans (ler_normB _ _) _; lra.
have hs := normr_ge0 s.
apply: le_lt_trans (ler_wpM2l hs hsum) _.
have -> : `|s| * (2 * e') = e * (`|s| / (`|s| + 1)).
  by rewrite /e'; field; lra.
have hq : `|s| / (`|s| + 1) < 1 by rewrite ltr_pdivrMr //; lra.
by rewrite -[X in _ < X]mulr1 ltr_pM2l.
Qed.


(** Source for [dgpr_gaussian_shift_exponent]: elementary estimate
    behind the domination in lem:classes(cl:div): if 0 <= x <= a + v,
    then -a^2/c <= v^2/c - x^2/(2c). *)
Lemma dgpr_gaussian_shift_exponent (c a x v : R) : 0 < c -> 0 <= a -> 0 <= x -> 0 <= v ->
  x <= a + v -> - a ^+ 2 / c <= v ^+ 2 / c + - x ^+ 2 / (2 * c).
Proof.
move=> hc ha hx hv hxav.
have h1 : x ^+ 2 <= 2 * a ^+ 2 + 2 * v ^+ 2.
  have h2 : x ^+ 2 <= (a + v) ^+ 2 by rewrite ler_pXn2r // nnegrE; lra.
  have h3 : 0 <= (a - v) ^+ 2 := sqr_ge0 _.
  have he : 2 * a ^+ 2 + 2 * v ^+ 2 = (a + v) ^+ 2 + (a - v) ^+ 2 by ring.
  lra.
have he : v ^+ 2 / c + - x ^+ 2 / (2 * c) - - a ^+ 2 / c =
    (2 * a ^+ 2 + 2 * v ^+ 2 - x ^+ 2) / (2 * c) by field; lra.
have hq : 0 <= (2 * a ^+ 2 + 2 * v ^+ 2 - x ^+ 2) / (2 * c) by apply: divr_ge0; lra.
lra.
Qed.

(** Source for [dgpr_gaussian_quotient_bound]: the domination of the
    difference quotients in lem:classes(cl:div), by the mean value
    inequality (Federer 2.2.7, p. 64, through 3.1.1, p. 210) on the
    convex ball with centre x and radius |v|. *)
Lemma dgpr_gaussian_quotient_bound (phi : X -> R) (Dphi : X -> Hom X R^o) (c s : R) (v x : X) :
  0 < c -> 0 < s -> s <= 1 ->
  (forall x, has_norm_differential NX NR setT phi x (Dphi x)) ->
  (forall x, exists L, 0 <= L /\ `|phi x| + L <= dgpr_gaussian_weight c (NX x) /\
     forall w, `|Dphi x w| <= L * NX w) ->
  `|s^-1 * (phi (x + s *: v) - phi x)| <=
    (NX v * c * E (NX v ^+ 2 / c)) * E (- NX x ^+ 2 / (2 * c)).
Proof.
move=> hc hs hs1 hd hb.
have hN := inner_norm_nonnegative (@euclidean_inner_productP R n).
pose U := [set y : X | NX (y - x) <= NX v].
pose M := c * E (NX v ^+ 2 / c) * E (- NX x ^+ 2 / (2 * c)).
have hU : is_inner_convex U.
  move=> y1 y2 h1 h2 t ht0 ht1; rewrite /U /=.
  have -> : (1 - t) *: y1 + t *: y2 - x = (1 - t) *: (y1 - x) + t *: (y2 - x).
    by rewrite !scalerBr addrACA -opprD -scalerDl subrK scale1r.
  apply: le_trans (real_seminorm_triangle hNX.1 _ _) _.
  rewrite !(real_seminorm_scale hNX.1) !ger0_norm //; last lra.
  have hl1 : (1 - t) * NX (y1 - x) <= (1 - t) * NX v by apply: ler_wpM2l => //; lra.
  have hl2 : t * NX (y2 - x) <= t * NX v by apply: ler_wpM2l.
  have -> : NX v = (1 - t) * NX v + t * NX v by ring.
  exact: lerD.
have hE0 := real_exponential_positive hE.
have hM : 0 <= M by rewrite /M; apply: mulr_ge0; [apply: mulr_ge0|]; apply: ltW => //.
have hDU : forall a, U a -> exists L : Hom X R^o,
    has_norm_differential NX NR setT phi a L /\ forall w, NR (L w) <= M * NX w.
  move=> a ha; exists (Dphi a); split; first exact: hd.
  have [L [hL0 [hL hLw]]] := hb a.
  have hLa : L <= c * E (- NX a ^+ 2 / c).
    by rewrite /dgpr_gaussian_weight in hL; have := normr_ge0 (phi a); lra.
  have hLM : L <= M.
    apply: le_trans hLa _; rewrite /M -mulrA; apply: ler_wpM2l; first exact: ltW.
    rewrite -(real_exponential_add hE) real_exponential_order.
    apply: dgpr_gaussian_shift_exponent => //.
    have -> : x = a + (x - a) by rewrite addrC subrK.
    apply: le_trans (real_seminorm_triangle hNX.1 _ _) _.
    by rewrite (real_seminorm_subtract hNX.1); apply: lerD.
  move=> w; apply: le_trans (hLw w) _; exact: ler_wpM2r.
have hxU : U x by rewrite /U /= subrr (real_seminorm_zero hNX.1).
have hsv : x + s *: v - x = s *: v by rewrite addrC addKr.
have hxsU : U (x + s *: v).
  rewrite /U /= hsv (real_seminorm_scale hNX.1) ger0_norm; last exact: ltW.
  by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r.
have hmv := norm_differential_convex_bound hNX hNR hU hM hDU hxsU hxU.
rewrite hsv (real_seminorm_scale hNX.1) (ger0_norm (ltW hs)) in hmv.
have hsi : 0 <= s^-1 by rewrite invr_ge0 ltW.
rewrite normrM (ger0_norm hsi).
apply: le_trans (ler_wpM2l hsi hmv) _.
have -> : s^-1 * (M * (s * NX v)) = M * NX v by field; apply: lt0r_neq0.
by rewrite /M le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(** Source for [dgpr_directional_integral]: lem:classes(cl:div) for a
    single direction. If phi is differentiable on R^n and
    |phi(x)| + ‖Dphi(x)‖ <= c exp(-|x|^2/c) for x in R^n, then
    ∫ Dphi(x)(v) dL^n x = 0. The difference quotients
    [x ↦ t^(-1) (phi(x + t v) - phi(x))] have integral 0 by the
    translation invariance of L^n (Federer 2.7.16, p. 135), are dominated
    by a Gaussian, and converge to Dphi(x)(v); Lebesgue's bounded
    convergence theorem (2.4.9, p. 85) concludes. *)
Lemma dgpr_directional_integral (phi : X -> R) (Dphi : X -> Hom X R^o) (c : R) (v : X) :
  0 < c ->
  (forall x, has_norm_differential NX NR setT phi x (Dphi x)) ->
  (forall x, exists L, 0 <= L /\ `|phi x| + L <= dgpr_gaussian_weight c (NX x) /\
     forall w, `|Dphi x w| <= L * NX w) ->
  is_measure_integral mu (real_total_integrand (fun x => Dphi x v)) 0%:E.
Proof.
move=> hc hd hb.
have hN := inner_norm_nonnegative (@euclidean_inner_productP R n).
have hcont := dgpr_differentiable_continuous hd.
pose t (k : nat) : R := (k.+1%:R)^-1.
have ht k : 0 < t k by rewrite /t invr_gt0 ltr0n.
have ht1 k : t k <= 1 by rewrite /t invf_le1 ?ler1n ?ltr0n.
pose f (k : nat) (x : X) : R := (t k)^-1 * (phi (x + t k *: v) - phi x).
pose H (x : X) : R := (NX v * c * E (NX v ^+ 2 / c)) * E (- NX x ^+ 2 / (2 * c)).
have h2c : 0 < 2 * c by rewrite mulr_gt0 // ltr0n.
have hH : summable_real_functions mu H.
  exact: (@summable_real_scale R _ mu hm _ _ (dgpr_gaussian_summable n h2c)).
have hfb k x : `|f k x| <= H x := dgpr_gaussian_quotient_bound v x hc (ht k) (ht1 k) hd hb.
have hfm k : is_measure_measurable_function mu
    (partial_function_total (f k : X -> real_line_metric R)).
  exact: (@norm_class_zero_scalar_real_measurable R X NX hNX mu hm
    (@euclidean_distribution_measure_open R n) (f k)
    (dgpr_quotient_class_zero (t k)^-1 (t k *: v) hcont)).
have hphim := dgpr_continuous_measurable (dgpr_continuous_class_zero hcont).
have hphib x : `|phi x| <= dgpr_gaussian_weight c (NX x).
  by have [L [hL0 [hL _]]] := hb x; lra.
have [a ha] := dgpr_dominated_summable hphim (dgpr_gaussian_weight_summable n hc) hphib.
have hfi k : is_measure_integral mu (real_total_integrand (f k)) 0%:E.
  have h1 := dgpr_translation_integral (t k *: v) ha.
  have h2 := real_total_integral_subtract hm h1 ha.
  have h3 := real_total_integral_scale hm ((t k)^-1) h2.
  by rewrite subrr mulr0 in h3.
have hconv x e : 0 < e -> exists N, forall k, (N <= k)%N -> `|f k x - Dphi x v| < e.
  move=> he.
  have hv1 : 0 < NX v + 1 by have := hN v; lra.
  pose e' := e / (NX v + 1).
  have he' : 0 < e' by rewrite /e' divr_gt0.
  have [d [hd0 hrem]] := norm_differential_remainder (hd x) he'.
  have hvd : 0 <= NX v / d by rewrite divr_ge0 // ltW.
  exists (Num.bound (NX v / d)) => k hk.
  have hk' : NX v / d < k.+1%:R.
    apply: lt_le_trans (archi_boundP hvd) _; rewrite ler_nat.
    exact: leq_trans hk (leqnSn k).
  have hsmall : NX (t k *: v) < d.
    rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW (ht k))) /t.
    by rewrite mulrC ltr_pdivrMr ?ltr0n // mulrC -ltr_pdivrMr.
  have hr := hrem (t k *: v) Logic.I hsmall.
  rewrite linearZ /= (real_seminorm_scale hNX.1) (ger0_norm (ltW (ht k))) in hr.
  have hti : 0 <= (t k)^-1 by rewrite invr_ge0 ltW.
  have -> : f k x - Dphi x v = (t k)^-1 * (phi (x + t k *: v) - phi x - t k * Dphi x v).
    by rewrite /f; field; apply: lt0r_neq0.
  rewrite normrM (ger0_norm hti).
  apply: le_lt_trans (ler_wpM2l hti hr) _.
  have -> : (t k)^-1 * (e' * (t k * NX v)) = e * (NX v / (NX v + 1)).
    by rewrite /e'; field; rewrite (lt0r_neq0 hv1) (lt0r_neq0 (ht k)).
  have hq : NX v / (NX v + 1) < 1 by rewrite ltr_pdivrMr //; lra.
  by rewrite -[X in _ < X]mulr1 ltr_pM2l.
have hgm : is_measure_measurable_function mu (real_total_integrand (fun x => Dphi x v)).
  exact: (dgpr_limit_measurable hfm hconv).
apply: (@real_dominated_integral_limit R _ mu hm f (fun x => Dphi x v) H (fun _ => 0) 0
  hH hgm hfb _ hfi _).
- by move=> x; apply: real_error_extended_order_limit => e he; exact: hconv x e he.
- apply: real_error_extended_order_limit => e he.
  by exists 0%N => k _; rewrite subrr normr0.
Qed.

(** Source for [dgpr_integral_zero_sum]: Federer 2.4.4(4), p. 82,
    through 2.5.1, p. 92: a finite sum of real functions with integral
    0 has integral 0. *)
Lemma dgpr_integral_zero_sum (I : finType) (F : I -> X -> R) :
  (forall i, is_measure_integral mu (real_total_integrand (F i)) 0%:E) ->
  is_measure_integral mu (real_total_integrand (fun x => \sum_i F i x)) 0%:E.
Proof.
move=> hF.
have h : forall s : seq I,
    is_measure_integral mu (real_total_integrand (fun x => \sum_(i <- s) F i x)) 0%:E.
  elim=> [|i s IH].
  - have -> : (fun x => \sum_(i <- [::]) F i x) = (fun _ => 0).
      by apply: funext=> x; rewrite big_nil.
    exact: real_total_zero_integral hm.
  - have -> : (fun x => \sum_(j <- i :: s) F j x) = (fun x => F i x + \sum_(j <- s) F j x).
      by apply: funext=> x; rewrite big_cons.
    by have := real_total_integral_add hm (hF i) IH; rewrite addr0.
exact: h.
Qed.

(** Source for [dgpr_two_neq0]: the characteristic hypothesis of the
    trace in Federer 1.4.5, p. 21, for the real field. *)
Lemma dgpr_two_neq0 : (1 + 1 : R) != 0.
Proof. by apply: lt0r_neq0; lra. Qed.

(** Source for [dgpr_divergence]: div g(x) = trace Dg(x), mr:notation,
    blueprint section 2, with the trace of Federer 1.4.5, p. 21,
    computed in the standard basis of R^n. *)
Definition dgpr_divergence (D : Hom X X) : R :=
  @trace_Hom R dgpr_two_neq0 X (Finite.clone 'I_n _)
    (@coordinate_basis R n) (@coordinate_basisP R n) D.

(** Source for [dgpr_divergenceE]: Federer 1.4.5, p. 21: the trace in
    the standard basis is the sum of the diagonal coordinates. *)
Lemma dgpr_divergenceE (D : Hom X X) :
  dgpr_divergence D = \sum_i D (@coordinate_basis R n i) i.
Proof.
rewrite /dgpr_divergence trace_HomE; apply: eq_bigr=> i _.
exact: euclidean_coordinate_dual_basis.
Qed.

(** Source for [dgpr_classes_div]: lem:classes(cl:div), first sentence,
    blueprint section 3. If g : R^n -> R^n is differentiable and
    |g(x)| + ‖Dg(x)‖ <= c exp(-|x|^2/c) for x in R^n, then
    ∫ div g dL^n = 0. *)
Theorem dgpr_classes_div (g : X -> X) (Dg : X -> Hom X X) (c : R) :
  0 < c ->
  (forall x, has_norm_differential NX NX setT g x (Dg x)) ->
  (forall x, exists L, 0 <= L /\ NX (g x) + L <= dgpr_gaussian_weight c (NX x) /\
     forall v, NX (Dg x v) <= L * NX v) ->
  is_measure_integral mu (real_total_integrand (fun x => dgpr_divergence (Dg x))) 0%:E.
Proof.
move=> hc hd hb.
have -> : (fun x => dgpr_divergence (Dg x)) =
    (fun x => \sum_i Dg x (@coordinate_basis R n i) i).
  by apply: funext=> x; exact: dgpr_divergenceE.
apply: dgpr_integral_zero_sum=> i.
pose M : Hom X R^o := dual_basis (@coordinate_basisP R n) i.
have hME y : M y = y i by exact: euclidean_coordinate_dual_basis.
have hM : norm_bounded_linear NX NR M.
  by exists 1; split=> // y; rewrite hME mul1r; exact: euclidean_coordinate_norm_bound.
have hdi x : has_norm_differential NX NR setT (fun y => M (g y)) x (hom_comp M (Dg x)).
  exact: (norm_differential_postcompose_linear hNX hNX hNR hM (hd x)).
have hbi x : exists L, 0 <= L /\ `|M (g x)| + L <= dgpr_gaussian_weight c (NX x) /\
    forall w, `|hom_comp M (Dg x) w| <= L * NX w.
  have [L [hL0 [hL hLw]]] := hb x; exists L; split=> //; split.
  - by apply: le_trans hL; rewrite lerD2r hME; exact: euclidean_coordinate_norm_bound.
  - move=> w; rewrite hom_compE hME; apply: le_trans (hLw w).
    exact: euclidean_coordinate_norm_bound.
have h := dgpr_directional_integral (@coordinate_basis R n i) hc hdi hbi.
have -> : (fun x => Dg x (@coordinate_basis R n i) i) =
    (fun x => hom_comp M (Dg x) (@coordinate_basis R n i)).
  by apply: funext=> x; rewrite hom_compE hME.
exact: h.
Qed.

Local Notation Zk k := (@ContinuousMultilinear.space R k X R^o NX NR hNX hNR).
Local Notation ev k := (@ContinuousMultilinear.evaluation R k X R^o NX NR hNX hNR).
Local Notation ZN k := (@ContinuousMultilinear.norm R k X R^o NX NR hNX hNR).
Local Notation lawsk k := (@ContinuousMultilinear.laws R k X R^o NX NR hNX hNR).

(** Source for [dgpr_laplacian]: Delta f(x) = trace D^2 f(x)
    = sum_i D^2 f(x)(eps_i, eps_i), mr:notation, blueprint section 2,
    for the second differential of Federer 3.1.11, p. 219. *)
Definition dgpr_laplacian (z : Zk 2) : R :=
  \sum_i ev 2 [ffun _ : 'I_2 => @coordinate_basis R n i] z.

(** Source for [dgpr_classes_laplacian]: lem:classes(cl:div), second
    sentence, blueprint section 3: if f : R^n -> R has Gaussian decay,
    then ∫ Delta f dL^n = 0. The field D2 is any field of second
    differentials of f; one exists since f is of class infinity. *)
Theorem dgpr_classes_laplacian (f : X -> R) (D2 : X -> Zk 2) :
  dgpr_gaussian_decay hNR f ->
  (forall x, dgpr_higher_differential hNX hNR setT f 2 x (D2 x)) ->
  is_measure_integral mu (real_total_integrand (fun x => dgpr_laplacian (D2 x))) 0%:E.
Proof.
move=> [_ hdec] hD2.
have [c1 [hc1 hb1]] := hdec 1%N.
have [c2 [hc2 hb2]] := hdec 2%N.
have hex1 x : exists w : Zk 1, dgpr_higher_differential hNX hNR setT f 1 x w.
  have [g [hg [L [hL _]]]] := hD2 x.
  exact: (norm_domain_interior_member hNX (norm_differential_interior hL)).
case: (choice hex1)=> D1 hD1.
have hDD1 a : exists L : Hom X (Zk 1), has_norm_differential NX (ZN 1) setT D1 a L /\
    forall u v, ev 1 u (L v) = ev 2 (multilinear_successor_arguments u v) (D2 a).
  have [g [hg [L [hL hev]]]] := hD2 a.
  have hgD : g = D1 by apply: funext=> x; exact: hg x (D1 x) (hD1 x).
  exists L; split=> //.
  rewrite -hgD; case: hL=> _ hLb hLr; split=> //.
  - by exists 1; split.
  - move=> e he; have [d [hd hr]] := hLr e he.
    by exists d; split=> // h _ hh; apply: hr=> //; exact: hex1.
have hZ1 := continuous_multilinear_norm_is_norm hNR (lawsk 1).
apply: dgpr_integral_zero_sum=> i.
pose u : {ffun 'I_1 -> X} := [ffun _ => @coordinate_basis R n i].
have hunit : NX (@coordinate_basis R n i) = 1 := @euclidean_coordinate_unit_norm R n i.
pose psi (x : X) : R := ev 1 u (D1 x).
have hM := continuous_multilinear_evaluation_bounded hNX (lawsk 1) u.
have hpsi a : exists M : Hom X R^o, has_norm_differential NX NR setT psi a M /\
    forall v, M v = ev 2 (multilinear_successor_arguments u v) (D2 a).
  have [L [hL hev]] := hDD1 a.
  exists (hom_comp (ev 1 u) L); split.
  - exact: (norm_differential_postcompose_linear hNX hZ1 hNR hM hL).
  - by move=> v; rewrite hom_compE hev.
case: (choice hpsi)=> Dpsi hDpsi.
have hdi x : has_norm_differential NX NR setT psi x (Dpsi x) by have [] := hDpsi x.
have hbi x : exists L, 0 <= L /\ `|psi x| + L <= dgpr_gaussian_weight (c1 + c2) (NX x) /\
    forall w, `|Dpsi x w| <= L * NX w.
  have hz2 := continuous_multilinear_norm_laws (lawsk 2) (D2 x).
  exists (ZN 2 (D2 x)); split; first exact: multilinear_operator_nonnegative hz2.
  split.
  - apply: le_trans (dgpr_gaussian_weight_sum (NX x) hc1 hc2).
    apply: lerD; last exact: hb2 x (D2 x) Logic.I (hD2 x).
    apply: le_trans (hb1 x (D1 x) Logic.I (hD1 x)).
    have hb := multilinear_operator_bound (continuous_multilinear_norm_laws (lawsk 1) (D1 x)) u.
    by rewrite big_ord1 ffunE hunit mulr1 in hb.
  - move=> w; have [_ hv] := hDpsi x; rewrite hv.
    have hb := multilinear_operator_bound hz2 (multilinear_successor_arguments u w).
    have hp : \prod_(j < 2) NX (multilinear_successor_arguments u w j) = NX w.
      rewrite /multilinear_successor_arguments multilinear_arguments_cast_product
        multilinear_arguments_product big_ord1 ffunE big_ord1 ffunE hunit mul1r.
      by [].
    by rewrite hp in hb.
have h := dgpr_directional_integral (@coordinate_basis R n i) (addr_gt0 hc1 hc2) hdi hbi.
have -> : (fun x => ev 2 [ffun _ : 'I_2 => @coordinate_basis R n i] (D2 x)) =
    (fun x => Dpsi x (@coordinate_basis R n i)).
  apply: funext=> x; have [_ hv] := hDpsi x.
  by rewrite hv multilinear_successor_constant_arguments.
exact: h.
Qed.

End Directional.
