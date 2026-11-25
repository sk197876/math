(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3;
    blueprint dgpr_blueprint.tex, proof of lem:identities(bounds):
    since mu0 <= mu, rho <= U on Omega_T.

    The general comparison: if mu0(A) <= mu(A) for every A, both measures
    are finite, k is a bounded nonnegative function whose sets
    {x : k(x) < c} are measurable for both measures, and k has the
    integrals I0 and I with respect to mu0 and mu (Federer 2.4.2), then
    I0 <= I. The proof compares k with the step functions
    sum_j (j+1) h 1_(B_j) and sum_j j h 1_(B_j) on the layers
    B_j = {x : j h <= k(x) < (j+1) h} (Federer 2.4.1, 2.4.2). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure CharacteristicFunctionUP CharacteristicFunctionSealed
  PartialExtendedOrderLoci MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralComparison
  MeasureCharacteristicIntegral MeasureFiniteCharacteristicIntegral SummableRealFunctionUP
  Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner ScalarInnerProduct CompleteMetricUP
  VectorDaniellHypotheses MeasurableFunctionUP RadonMeasureUP NormDifferentialUP NormClassOneUP
  NormBoundedLinearTopology NormOpenPreimage SmoothFunctionSpaceUP SmoothTestSpaces
  DistributionVariationUP FunctionLatticeUP CompactSupportFunctionUP.
From DPGPR Require Import DgprHeatKernel DgprHeatExtension DgprHeatSemiconvex DgprStanding DgprHeatObjects
  DgprIdentities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Layers.
Variable R : realType.

(** Source for [dgpr_layer_exists]: for 0 < h and 0 <= y < J h there is
    j < J with j h <= y < (j+1) h; supporting the step functions of
    Federer 2.4.1 in the proof of lem:identities(bounds). *)
Lemma dgpr_layer_exists (h y : R) (J : nat) : 0 < h -> 0 <= y -> y < J%:R * h ->
  exists j : 'I_J, j%:R * h <= y < j.+1%:R * h.
Proof.
move=> hh hy; elim: J => [|J IH] hJ.
  by move: hJ; rewrite mul0r => /(le_lt_trans hy); rewrite ltxx.
case: (ltP y (J%:R * h)) => hyJ.
  by have [j hj] := IH hyJ; exists (widen_ord (leqnSn J) j).
by exists (@ord_max J); rewrite /= hyJ hJ.
Qed.

(** Source for [dgpr_layer_unique]: the layers [j h, (j+1) h) are
    disjoint; supporting lem:identities(bounds). *)
Lemma dgpr_layer_unique (h y : R) (i j : nat) : 0 < h ->
  i%:R * h <= y < i.+1%:R * h -> j%:R * h <= y < j.+1%:R * h -> i = j.
Proof.
move=> hh /andP [hi1 hi2] /andP [hj1 hj2].
have h1 : (i < j.+1)%N by rewrite -(ltr_nat R) -(ltr_pM2r hh); exact: le_lt_trans hi1 hj2.
have h2 : (j < i.+1)%N by rewrite -(ltr_nat R) -(ltr_pM2r hh); exact: le_lt_trans hj1 hi2.
by apply/eqP; rewrite eqn_leq -ltnS h1 -ltnS h2.
Qed.
End Layers.

Section Comparison.
Variable R : realType.
Variable X : choiceType.
Local Notation chi := (@CharacteristicFunction.value R X).
Local Notation chiP := (@CharacteristicFunction.laws R X).
Variables mu mu0 : set X -> \bar R.
Hypothesis hm : is_measure mu.
Hypothesis hm0 : is_measure mu0.
Hypothesis hle : forall A, (mu0 A <= mu A)%E.
Variables a b : R.
Hypothesis ha : mu setT = a%:E.
Hypothesis hb : mu0 setT = b%:E.
Variable k : X -> R.
Hypothesis hlev : forall c : R,
  measure_measurable mu [set x | k x < c] /\ measure_measurable mu0 [set x | k x < c].
Hypothesis hk0 : forall x, 0 <= k x.
Variable M : R.
Hypothesis hkM : forall x, k x <= M.

(** Source for [dgpr_layer]: the layer B_j = {x : j h <= k(x) < (j+1) h};
    supporting lem:identities(bounds). *)
Definition dgpr_layer (h : R) (j : nat) : set X := [set x | j%:R * h <= k x < j.+1%:R * h].

(** Source for [dgpr_layer_measurable]: B_j is the difference of two sets
    {x : k(x) < c}, hence measurable (Federer 2.1.3); supporting
    lem:identities(bounds). *)
Lemma dgpr_layer_measurable (nu : set X -> \bar R) (hn : is_measure nu) (h : R) (j : nat) :
  (forall c : R, measure_measurable nu [set x | k x < c]) -> measure_measurable nu (dgpr_layer h j).
Proof.
move=> hc.
have -> : dgpr_layer h j = [set x | k x < j.+1%:R * h] `\` [set x | k x < j%:R * h].
  apply/seteqP; split => x; rewrite /dgpr_layer /=.
  - move=> /andP [h1 h2]; split => //; apply/negP; by rewrite -leNgt.
  - by move=> [h2 /negP h1]; rewrite h2 andbT leNgt.
exact: (measure_measurable_difference hn (hc _) (hc _)).
Qed.

(** Source for [dgpr_finite_measure_fine]: a set of finite measure has the
    real value of its measure; supporting lem:identities(bounds). *)
Lemma dgpr_finite_measure_fine (nu : set X -> \bar R) (hn : is_measure nu) (c : R) (A : set X) :
  nu setT = c%:E -> nu A = (fine (nu A))%:E.
Proof.
move=> hc; have h0 := measure_nonnegative hn A; have h1 := measure_mono hn (subsetT A).
rewrite hc in h1; rewrite fineK // ge0_fin_numE //; exact: (le_lt_trans h1 (ltry _)).
Qed.

(** Source for [dgpr_layer_sum]: if x lies in B_(j0), then the sum of
    c_j 1_(B_j)(x) over j <= J equals c_(j0); supporting
    lem:identities(bounds). *)
Lemma dgpr_layer_sum (h : R) (J : nat) (c : nat -> R) (x : X) (j0 : 'I_J.+1) :
  0 < h -> dgpr_layer h j0 x -> \sum_(j < J.+1) c j * chi (dgpr_layer h j) x = c j0.
Proof.
move=> hh hx; rewrite (bigD1 j0) //= (characteristic_on_set (chiP _) hx) mulr1 big1 ?addr0 // => j hj.
rewrite (characteristic_off_set (chiP _)) ?mulr0 // => hjx.
by move/eqP: hj; apply; apply: val_inj; exact: (dgpr_layer_unique hh hjx hx).
Qed.

(** Source for [dgpr_layer_member]: if k(x) <= M < J h, then x lies in
    some B_j with j <= J; supporting lem:identities(bounds). *)
Lemma dgpr_layer_member (h : R) (J : nat) (x : X) : 0 < h -> M < J%:R * h ->
  exists j0 : 'I_J.+1, dgpr_layer h j0 x.
Proof.
move=> hh hJ; apply: (dgpr_layer_exists hh (hk0 x)).
apply: (le_lt_trans (hkM x)); apply: (lt_le_trans hJ).
by rewrite ler_pM2r // ler_nat.
Qed.

(** Source for [dgpr_integral_measure_comparison]: if mu0(A) <= mu(A) for
    every A, then the integral of k with respect to mu0 is at most its
    integral with respect to mu (Federer 2.4.2); for 0 < h, the step
    functions sum_j (j+1) h 1_(B_j) and sum_j j h 1_(B_j) lie above and
    below k, whence I0 <= I + h mu0(X). Supporting lem:identities(bounds),
    rho <= U. *)
Theorem dgpr_integral_measure_comparison (I0 I : R) :
  is_measure_integral mu0 (real_total_integrand k) I0%:E ->
  is_measure_integral mu (real_total_integrand k) I%:E -> I0 <= I.
Proof.
move=> hI0 hI.
have hb0 : 0 <= b by rewrite -lee_fin -hb; exact: (measure_nonnegative hm0 setT).
have hsetT : measure_measurable mu0 setT.
  rewrite -setC0; apply: measure_measurable_complement.
  exact: (measure_null_measurable hm0 (measure_empty hm0)).
apply/ler_addgt0Pr => e he.
pose h := e / (b + 1).
have hh : 0 < h by rewrite /h divr_gt0 //; lra.
have hhb : h * b < e.
  rewrite /h mulrAC ltr_pdivrMr; last by lra.
  by rewrite ltr_pM2l //; lra.
pose J := Num.bound (`|M| / h).
have hJ : M < J%:R * h.
  have hM : `|M| / h < J%:R := archi_boundP (divr_ge0 (normr_ge0 M) (ltW hh)).
  rewrite -ltr_pdivrMr //; apply: le_lt_trans hM.
  by apply: ler_wpM2r; [rewrite invr_ge0 ltW | exact: ler_norm].
pose m0 (j : nat) := fine (mu0 (dgpr_layer h j)).
pose m (j : nat) := fine (mu (dgpr_layer h j)).
have em0 j : mu0 (dgpr_layer h j) = (m0 j)%:E := dgpr_finite_measure_fine hm0 _ hb.
have em j : mu (dgpr_layer h j) = (m j)%:E := dgpr_finite_measure_fine hm _ ha.
have hmm j : m0 j <= m j by rewrite -lee_fin -em0 -em.
have hm0j j : 0 <= m0 j by rewrite -lee_fin -em0; exact: (measure_nonnegative hm0 _).
have hmeas0 j : measure_measurable mu0 (dgpr_layer h j).
  by apply: (dgpr_layer_measurable hm0) => c; exact: (hlev c).2.
have hmeas j : measure_measurable mu (dgpr_layer h j).
  by apply: (dgpr_layer_measurable hm) => c; exact: (hlev c).1.
have hpos (j : nat) : 0 < j.+1%:R * h by apply: mulr_gt0; rewrite ?ltr0Sn.
(* the upper step function *)
have hU := @measure_finite_positive_characteristic_integral R X 'I_J.+1 mu0 hm0 (index_enum 'I_J.+1)
  (fun j => dgpr_layer h j) (fun j => chi (dgpr_layer h j)) (fun j => j.+1%:R * h)
  (fun j _ => chiP _) (fun j _ => hmeas0 j) (fun j _ => hpos j).
have E1 : I0 <= \sum_(j < J.+1) j.+1%:R * h * m0 j.
  rewrite -lee_fin -sumEFin.
  have -> : (\sum_(j < J.+1) (j.+1%:R * h * m0 j)%:E)%E =
      (\sum_(j <- index_enum 'I_J.+1) (j.+1%:R * h)%:E * mu0 (dgpr_layer h j))%E.
    by apply: eq_bigr => j _; rewrite em0 EFinM.
  apply: (measure_integral_monotone hm0 hI0 hU).
  apply: (measure_almost_everywhere_mono hm0 _ (measure_almost_everywhere_true hm0)) => x _.
  have [j0 hj0] := dgpr_layer_member x hh hJ.
  exists (k x)%:E, (\sum_(j <- index_enum 'I_J.+1) j.+1%:R * h * chi (dgpr_layer h j) x)%:E.
  split; first by apply/real_total_integrand_graph.
  split; first by eexists; split; reflexivity.
  rewrite lee_fin (dgpr_layer_sum (fun j => j.+1%:R * h) hh hj0).
  have /andP [_ hj2] : (j0%:R * h <= k x < j0.+1%:R * h) := hj0.
  exact: ltW.
have hrecl (F : nat -> R) : \sum_(j < J.+1) F j = F 0%N + \sum_(i < J) F i.+1.
  by rewrite big_ord_recl; congr (_ + _); apply: eq_bigr => i _; rewrite lift0.
(* the lower step function *)
have hL := @measure_finite_positive_characteristic_integral R X 'I_J mu hm (index_enum 'I_J)
  (fun i => dgpr_layer h i.+1) (fun i => chi (dgpr_layer h i.+1)) (fun i => i.+1%:R * h)
  (fun i _ => chiP _) (fun i _ => hmeas i.+1) (fun i _ => hpos i).
have E2 : \sum_(i < J) i.+1%:R * h * m i.+1 <= I.
  rewrite -lee_fin -sumEFin.
  have -> : (\sum_(i < J) (i.+1%:R * h * m i.+1)%:E)%E =
      (\sum_(i <- index_enum 'I_J) (i.+1%:R * h)%:E * mu (dgpr_layer h i.+1))%E.
    by apply: eq_bigr => i _; rewrite em EFinM.
  apply: (measure_integral_monotone hm hL hI).
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm)) => x _.
  have [j0 hj0] := dgpr_layer_member x hh hJ.
  exists (\sum_(i <- index_enum 'I_J) i.+1%:R * h * chi (dgpr_layer h i.+1) x)%:E, (k x)%:E.
  split; first by eexists; split; reflexivity.
  split; first by apply/real_total_integrand_graph.
  rewrite lee_fin.
  have -> : \sum_(i <- index_enum 'I_J) i.+1%:R * h * chi (dgpr_layer h i.+1) x =
      \sum_(j < J.+1) j%:R * h * chi (dgpr_layer h j) x.
    rewrite (hrecl (fun j => j%:R * h * chi (dgpr_layer h j) x)) /= ?mulr0n !mul0r add0r.
    by [].
  rewrite (dgpr_layer_sum (fun j => j%:R * h) hh hj0).
  by have /andP [hj1 _] : (j0%:R * h <= k x < j0.+1%:R * h) := hj0.
(* the total mass of the layers *)
have hC := @measure_finite_positive_characteristic_integral R X 'I_J.+1 mu0 hm0 (index_enum 'I_J.+1)
  (fun j => dgpr_layer h j) (fun j => chi (dgpr_layer h j)) (fun _ => 1)
  (fun j _ => chiP _) (fun j _ => hmeas0 j) (fun _ _ => ltr01).
have hT := measure_characteristic_integral hm0 (chiP setT) hsetT.
have E3 : \sum_(j < J.+1) m0 j <= b.
  rewrite -lee_fin -sumEFin -hb.
  have -> : (\sum_(j < J.+1) (m0 j)%:E)%E =
      (\sum_(j <- index_enum 'I_J.+1) 1%:E * mu0 (dgpr_layer h j))%E.
    by apply: eq_bigr => j _; rewrite em0 mul1e.
  apply: (measure_integral_monotone hm0 hC hT).
  apply: (measure_almost_everywhere_mono hm0 _ (measure_almost_everywhere_true hm0)) => x _.
  have [j0 hj0] := dgpr_layer_member x hh hJ.
  exists (\sum_(j <- index_enum 'I_J.+1) 1 * chi (dgpr_layer h j) x)%:E, (chi setT x)%:E.
  split; first by eexists; split; reflexivity.
  split; first by eexists; split; reflexivity.
  rewrite lee_fin (dgpr_layer_sum (fun _ => 1) hh hj0).
  by rewrite (characteristic_on_set (chiP setT) (Logic.I : setT x)).
(* the arithmetic *)
have s1 : \sum_(j < J.+1) j.+1%:R * h * m0 j =
    \sum_(j < J.+1) j%:R * h * m0 j + h * \sum_(j < J.+1) m0 j.
  rewrite mulr_sumr -big_split; apply: eq_bigr => j _ /=.
  by rewrite -natr1; ring.
have s2 : \sum_(j < J.+1) j%:R * h * m0 j <= \sum_(i < J) i.+1%:R * h * m i.+1.
  rewrite (hrecl (fun j => j%:R * h * m0 j)) /= ?mulr0n !mul0r add0r.
  apply: ler_sum => i _.
  by apply: ler_wpM2l; [rewrite mulr_ge0 // ltW | exact: hmm].
have s3 : h * \sum_(j < J.+1) m0 j <= h * b by apply: ler_wpM2l; [exact: ltW|].
apply: (le_trans E1); rewrite s1.
apply: (le_trans (lerD s2 s3)).
apply: lerD; [exact: E2 | exact: ltW].
Qed.
End Comparison.

Section KernelSublevels.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation p := (@dgpr_heat_kernel R n).

(** Source for [dgpr_scalar_sublevel_open]: {r : r < c} is open in R
    (Federer 2.2.1); supporting lem:identities(bounds). *)
Lemma dgpr_scalar_sublevel_open (c : R) : @open (real_norm_metric_space hA) [set r : R^o | r < c].
Proof.
rewrite openE => r hr; apply: (proj1 (norm_domain_interior_neighbourhood hA _ r)).
exists (c - r); split; first by rewrite subr_gt0.
move=> h hh /=; have := ler_norm h; move: hr hh; change (r < c -> `|h| < c - r -> h <= `|h| -> r + h < c).
lra.
Qed.

(** Source for [dgpr_kernel_sublevel_open]: for 0 < s, x in R^n and c in
    R, the set {y : p_s(x - y) < c} is open, since [y |-> p_s(x - y)] is
    continuous (def:heat); supporting lem:identities(bounds). *)
Lemma dgpr_kernel_sublevel_open (s : R) (x : X) (c : R) : 0 < s ->
  @open (real_norm_metric_space hN) [set y | p s (x - y) < c].
Proof.
move=> hs.
have hk := dgpr_reflect_class_zero x (dgpr_kernel_class_zero hs).
have h := @norm_class_zero_open_preimage R X R^o N A1 hN hA _ _ _ hk (@dgpr_scalar_sublevel_open c).
have e : [set y : X | True /\ [set r : R^o | r < c] (p s (x - y))] = [set y | p s (x - y) < c].
  by apply/seteqP; split => y /=; [case | split].
by rewrite -e.
Qed.
End KernelSublevels.

Section RhoU.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation p := (@dgpr_heat_kernel R n).
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
Local Notation ND := (hom_norm hCY (scalar_inner_productP R) heY).
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
Local Notation hmu0 := (dgpr_standing_mu0_measure hS).
Local Notation hOmu := (dgpr_standing_mu_borel hS).
Local Notation hOmu0 := (dgpr_standing_mu0_borel hS).
Local Notation hMmu := (dgpr_standing_mu_mass hS).
Local Notation hMmu0 := (dgpr_standing_mu0_mass hS).
Local Notation U := (dgpr_heat_U hS).
Local Notation W := (dgpr_heat_W hS).
Local Notation S := (dgpr_heat_S hS).
Local Notation rho := (dgpr_heat_rho hS).
Local Notation B := (dgpr_heat_B hS).
Local Notation eta := (dgpr_heat_eta hS).
Local Notation kappa := (dgpr_heat_kappa hS).

(** Source for [dgpr_identities_rho_le_U]: blueprint proof of
    lem:identities(bounds), "since mu0 <= mu, we have rho <= U": rho(t,x)
    and U(t,x) are the integrals of [y |-> p_(T-t)(x-y)] with respect to
    mu0 and mu, and [dgpr_integral_measure_comparison] applies. *)
Theorem dgpr_identities_rho_le_U (t : R) (x : X) : t < T -> rho (t, x) <= U (t, x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have hU := dgpr_unit_kernel_integral hmu hOmu hMmu x hs.
have hR := dgpr_unit_kernel_integral hmu0 hOmu0 hMmu0 x hs.
have hlev (c : R) : measure_measurable mu [set y | p (T - t) (x - y) < c] /\
    measure_measurable mu0 [set y | p (T - t) (x - y) < c].
  by split; [apply: hOmu | apply: hOmu0]; exact: dgpr_kernel_sublevel_open.
have hk0 (y : X) : 0 <= p (T - t) (x - y) by exact: ltW (dgpr_kernel_gt0 _ hs).
have hkM (y : X) : p (T - t) (x - y) <= dgpr_kernel_constant n (T - t).
  exact: le_trans (ler_norm _) (dgpr_kernel_abs_le _ hs).
exact: (dgpr_integral_measure_comparison hmu hmu0 (dgpr_standing_mu0_le hS) hMmu hMmu0 hlev hk0 hkM hR hU).
Qed.

(** Source for [dgpr_identities_bounds_full]: blueprint
    lem:identities(bounds) in full: 0 < rho <= U <= S, kappa >= 0,
    U^(-1) W in K, |B| <= Lambda and ||eta|| <= (T - t)^(-1/2) on
    Omega_T. *)
Theorem dgpr_identities_bounds_full (t : R) (x : X) : t < T ->
  [/\ 0 < rho (t, x) /\ rho (t, x) <= U (t, x), U (t, x) <= S (t, x), 0 <= kappa (t, x),
      K ((U (t, x))^-1 *: W (t, x)) /\ NH (B (t, x)) <= Lam & ND (eta (t, x)) <= (Num.sqrt (T - t))^-1].
Proof.
move=> ht; have [[h1 h2] h3 h4 h5 h6] := dgpr_identities_bounds hS x ht.
by split => //; split => //; exact: dgpr_identities_rho_le_U.
Qed.
End RhoU.
