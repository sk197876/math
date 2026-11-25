(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:main (Theorem 1.1 of DPGPR 2026 for rectifiable data): the
    deduction of thm:main from lem:compact_case by cut-off functions.

    Suppose that the data of mr:hypotheses_main
    ([dgpr_main_hypotheses], DgprMainHypotheses.v) are given, with
    μ = (H^k ⌞ M) ⌞ θ. Let 0 < ϱ < ∞, let φ_ϱ be the cut-off function of
    [dgpr_main_cutoff] (DgprMainCutoff.v), with 0 ≤ φ_ϱ ≤ 1, φ_ϱ = 1 on
    B(0, ϱ), φ_ϱ = 0 outside U(0, 2ϱ) and |Dφ_ϱ(x)(v)| ≤ c_0 ϱ^{-1} |v|,
    and let P g = φ_ϱ g for g ∈ D(R^n, Y) ([dgpr_test_multiplier]). Set
    θ_ϱ = φ_ϱ θ, so that μ_ϱ = (H^k ⌞ M) ⌞ θ_ϱ, and
        Υ_ϱ(g) = Υ(φ_ϱ g) + ∫ X • (Dφ_ϱ · g) dμ    for g ∈ D(R^n, Y),
    where Dφ_ϱ(x) · g(x) is the map [v ↦ Dφ_ϱ(x)(v) g(x)]
    ([dgpr_rank_one]). Since D(φ_ϱ g) = Dφ_ϱ · g + φ_ϱ Dg
    ([dgpr_product_differential]), the constraint Υ(φ_ϱ g) = −σ(D(φ_ϱ g))
    yields Υ_ϱ(g) = −∫ X • Dg dμ_ϱ. If |g| ≤ m, then
    Υ_ϱ(g) ≤ m (‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n)); hence Υ_ϱ has a
    variation measure ‖Υ_ϱ‖ with ‖Υ_ϱ‖(R^n) ≤ ‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n)
    ([dgpr_bounded_variation_measure], DgprMainVariation.v). The data
    with θ_ϱ, Υ_ϱ and ‖Υ_ϱ‖ satisfy mr:hypotheses_main, and μ_ϱ vanishes
    outside B(0, 2ϱ). The compact case therefore yields
        μ(U(0, ϱ)) ≤ μ_ϱ(R^n)
                   ≤ C H^k(M)^{1/k} (‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n))
    ([dgpr_cutoff_bound]), and the limit ϱ → ∞ gives thm:main
    ([dgpr_main_from_cutoff_bound], [dgpr_main_from_compact_case]).

    The blueprint bounds the variation of Υ_ϱ by the measure
    ν_ϱ = φ_ϱ ‖Υ‖ + c_0 ϱ^{-1} |X| μ; here only its total mass is
    bounded, which suffices (docs/divergences.md). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology ring lra.
From Federer Require Import Hom Bilinear RealNormUP NormMetric InnerProductUP InnerNorm InnerProductLaws
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis
  HomInner InnerConvex InnerMetric RealMetricBackground ExtendedRealOrderTopology ExtendedRealOrderLimit
  NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormRegularity SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureRestriction MeasureDensity MeasurableFunctionUP
  MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  SummableRealArithmetic RealIntegralLinearMapExistence MeasureContinuityBelow RadonMeasureUP
  FunctionLatticeUP CompactSupportFunctionUP DistributionVariationUP HausdorffMeasure RectifiableSetUP
  TopologicalBorel BorelFunctionUP BorelFunctionBasic RealPower.
From DPGPR Require Import DgprHomNorms DgprMichaelSimon DgprVarifoldWeight DgprMainHypotheses
  DgprMainHypothesesCompact DgprUpperEntropy DgprCompactCase DgprCompactCaseGeneral
  DgprMainVariation DgprMainCutoff DgprMainMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CutoffArgument.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space BX).
Local Notation NT := (real_norm_metric_space hN).
Local Notation HK := (@hausdorff_measure R RnM k).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation HI := (hom_inner BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Local Notation HT := (real_norm_metric_space hNH).
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Local Notation DT := (smooth_test_space hE).
Local Notation tv := (smooth_test_value hE).
Variable K : set HT.
Variables lam Lam C : R.
Variable M : set RnM.
Variable theta : X -> R.
Variable Xf : X -> Hom X Y.
Variable Ups : Hom DT R^o.
Variable ups : set NT -> \bar R.
Hypothesis H : @dgpr_main_hypotheses R n k hk Y CY hCY d eY E ev hE K lam Lam M theta Xf Ups ups.
Hypothesis hC : 0 <= C.
Hypothesis hcc : dgpr_compact_case_inequality hk lam Lam C.
Local Notation HM := (measure_restrict HK M).
Local Notation mu := (dgpr_main_measure k M theta).

Let heY : is_basis eY := dgpr_main_Y_basis H.
Let htheta : forall x, M x -> 0 <= theta x := dgpr_main_theta_nonnegative H.
Let hsum : summable_real_functions HM theta := dgpr_main_theta_summable H.
Let hHMm : is_measure HM := measure_restrict_is_measure (hausdorff_measure_is_measure RnM k) M.
Let hmu : is_measure mu := dgpr_density_measure_is_measure k htheta.

(** Source for [dgpr_test_differential]: Federer 4.1.1, p. 344, and
    3.1.1, p. 210: every g ∈ D(R^n, Y) has a differential Dg(x) at each
    x ∈ R^n. Supporting lemma. *)
Lemma dgpr_test_differential (g : DT) :
  exists Dg : X -> Hom X Y, forall x, has_norm_differential N NY setT (tv g) x (Dg x).
Proof.
have [D0 hD0] := (norm_class_firstP hN hNY setT (tv g)).1 (smooth_test_value_smooth hE g 1%N).
by exists D0 => x; exact: (norm_class_one_differential hD0 (Logic.I : setT x)).
Qed.

(** Source for [dgpr_test_differential_measurable]: Federer 3.1.1,
    p. 210, and 2.3.2, p. 73: the differential Dg of g ∈ D(R^n, Y) is
    continuous, hence H^k ⌞ M measurable. Supporting lemma. *)
Lemma dgpr_test_differential_measurable (g : DT) (Dg : X -> Hom X Y) :
  (forall x, has_norm_differential N NY setT (tv g) x (Dg x)) ->
  is_measure_measurable_function HM (partial_function_total (fun x => (Dg x : HT))).
Proof.
move=> hD.
have [D0 hD0] := (norm_class_firstP hN hNY setT (tv g)).1 (smooth_test_value_smooth hE g 1%N).
have -> : Dg = D0.
  apply: funext => x.
  exact: (norm_differential_unique hN hNY (hD x) (norm_class_one_differential hD0 (Logic.I : setT x))).
apply: dgpr_borel_restrict_measurable; apply: continuous_borel_function.
exact: (dgpr_differential_field_continuous (norm_class_one_continuity hD0)).
Qed.

(** Source for [dgpr_cutoff_bound]: blueprint proof of thm:main: there
    is 0 < c_0 < ∞ such that, for 0 < ϱ < ∞,
        μ(U(0, ϱ)) ≤ C H^k(M)^{1/k} (‖Υ‖(R^n) + c_0 ϱ^{-1} Λ μ(R^n)).
    The proof applies lem:compact_case, through the hypothesis on C, to
    θ_ϱ = φ_ϱ θ and Υ_ϱ(g) = Υ(φ_ϱ g) + ∫ X • (Dφ_ϱ · g) dμ. Direct
    formalisation. *)
Lemma dgpr_cutoff_bound : exists c : R, 0 < c /\ forall r : R, 0 < r ->
  (mu [set y | (N y < r)%R] <=
    ((C * real_power (fine (HK M)) (k%:R)^-1) *
      (fine (ups setT) + c / r * Lam * fine (mu setT)))%:E)%E.
Proof.
have [c [hc hcut]] := dgpr_main_cutoff R n.
exists c; split=> // r hr.
have [w [hw01 hw1 hw0 hws hwD]] := hcut r hr.
have [[Dw hDw] hwc] := dgpr_smooth_real_differential hws.
have [P hP] := dgpr_test_multiplier hE hws.
have [a ha] := dgpr_density_measure_finite htheta hsum.
have hw0' : forall x, 0 <= w x by move=> x; have /andP [] := hw01 x.
have hcr : 0 <= c / r by rewrite divr_ge0 // ltW.
have hHMw : is_measure_measurable_function HM (real_total_integrand w).
  apply: (@measurable_partial_real_embedding R RnM _ hHMm).
  apply: dgpr_borel_restrict_measurable; exact: continuous_borel_function hwc.
have hmuw : is_measure_measurable_function mu (real_total_integrand w).
  exact: (@dgpr_density_measure_function R n k M theta htheta _ (real_total_integrand w) hHMw).
have hconstr := dgpr_main_constraint H.
have hXm := dgpr_main_X_measurable H.
pose F (g : DT) (x : X) := HI (Xf x) (dgpr_rank_one (Dw x) (tv g x)).
have hdec (g : DT) (Dg : X -> Hom X Y) :
    (forall x, has_norm_differential N NY setT (tv g) x (Dg x)) ->
    (forall x, has_norm_differential N NY setT (tv (P g)) x
      (dgpr_rank_one (Dw x) (tv g x) + w x *: Dg x)) /\
    (forall x, HI (Xf x) (dgpr_rank_one (Dw x) (tv g x) + w x *: Dg x) =
      F g x + w x * HI (Xf x) (Dg x)).
  move=> hD; split=> x.
  - have -> : tv (P g) = (fun y => w y *: tv g y) by apply: funext => y; exact: hP.
    exact: (dgpr_product_differential hNY (hDw x) (hD x)).
  - by rewrite (bilDr (inner_bilinear BH)) (bilZr (inner_bilinear BH)).
have hFm (g : DT) : is_measure_measurable_function mu (real_total_integrand (F g)).
  have [Dg hD] := dgpr_test_differential g.
  have [hPD hid] := hdec g Dg hD.
  have h1 := (hconstr (P g) _ hPD).1.
  have h2 := (hconstr g Dg hD).1.
  have h3 := dgpr_real_total_multiply_measurable hmu hmuw h2.
  have h4 := dgpr_real_total_subtract_measurable hmu h1 h3.
  suff -> : F g = (fun x => HI (Xf x) (dgpr_rank_one (Dw x) (tv g x) + w x *: Dg x) -
      w x * HI (Xf x) (Dg x)) by exact: h4.
  by apply: funext => x; rewrite hid addrK.
have hFb (g : DT) (m : R) : (forall x, NY (tv g x) <= m) ->
    forall x, M x -> `|F g x| <= c / r * Lam * m.
  move=> hm x hx.
  apply: le_trans (dgpr_rank_one_inner_bound hCY heY (Xf x) (tv g x) hcr (hwD x (Dw x) (hDw x))) _.
  have hX : NH (Xf x) <= Lam := dgpr_main_K_norm H (dgpr_main_X_values H hx).
  have hX0 : 0 <= NH (Xf x) by rewrite /hom_norm; exact: inner_norm_nonnegative.
  apply: ler_pM; first exact: mulr_ge0.
  - exact: inner_norm_nonnegative.
  - exact: ler_wpM2l.
  - exact: hm.
have hFs (g : DT) : exists b : R, is_measure_integral mu (real_total_integrand (F g)) b%:E.
  have [m hm] := dgpr_compact_function_bounded (dgpr_test_norm_compact g).
  have [b [hb _]] := dgpr_bounded_integral hmu ha (dgpr_density_measure_on k M theta) (hFm g)
    (hFb g m hm).
  by exists b.
have hFlin (t : R) (g h : DT) (x : X) : F (t *: g + h) x = t * F g x + F h x.
  have hv : tv (t *: g + h) x = t *: tv g x + tv h x.
    exact: (congr1 (fun q : X -> Y => q x) (smooth_test_values_linear hE t g h)).
  have hr1 : dgpr_rank_one (Dw x) (tv (t *: g + h) x) =
      t *: dgpr_rank_one (Dw x) (tv g x) + dgpr_rank_one (Dw x) (tv h x).
    apply: hom_ext => v.
    by rewrite hom_addE hom_scaleE !dgpr_rank_oneE hv scalerDr !scalerA mulrC.
  by rewrite /F hr1 (bilDr (inner_bilinear BH)) (bilZr (inner_bilinear BH)).
have [J hJ] := @real_integral_linear_map_exists R RnM DT mu hmu F hFlin hFs.
pose Ups' : Hom DT R^o := hom_comp Ups P + J.
have hupsm := dgpr_main_ups_measure H.
have hgauge := dgpr_main_ups_gauge H.
have hupsf := dgpr_main_ups_finite H.
pose Bd := fine (ups setT) + c / r * Lam * a.
have hS (phi : DT) (m : R) : (forall x, NY (tv phi x) <= m) -> Ups' phi <= m * Bd.
  move=> hm.
  have hPm : forall x, NY (tv (P phi) x) <= m.
    move=> x; rewrite hP inner_normZ ger0_norm //.
    apply: le_trans (hm x); rewrite -[X in _ <= X]mul1r ler_wpM2r //.
      exact: inner_norm_nonnegative.
    by have /andP [] := hw01 x.
  have h1 := dgpr_test_variation_bound hupsm hgauge hupsf hPm.
  have [b [hb hbK]] := dgpr_bounded_integral hmu ha (dgpr_density_measure_on k M theta) (hFm phi)
    (hFb phi m hm).
  have hJb : J phi = b := congr1 (@fine R) (measure_integral_unique (hJ phi) hb).
  rewrite /Ups' hom_addE hom_compE hJb /Bd mulrDr.
  apply: lerD => //; apply: le_trans hbK _.
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
have [ups' [hups'm hups'r hups'g hups'B]] := dgpr_bounded_variation_measure heY hS.
pose theta' := fun x => w x * theta x.
have hw01M : forall x, M x -> 0 <= w x <= 1 by move=> x _; exact: hw01 x.
have htheta' : forall x, M x -> 0 <= theta' x.
  by move=> x hx; rewrite /theta' mulr_ge0 //; exact: htheta.
have H' : @dgpr_main_hypotheses R n k hk Y CY hCY d eY E ev hE K lam Lam M theta' Xf Ups' ups'.
  constructor.
  - exact: dgpr_main_Y_basis H.
  - exact: dgpr_main_K_nonempty H.
  - exact: dgpr_main_K_compact H.
  - exact: dgpr_main_K_convex H.
  - exact: dgpr_main_lambda H.
  - exact: dgpr_main_Lambda H.
  - exact: dgpr_main_K_sv H.
  - exact: dgpr_main_K_norm H.
  - exact: dgpr_main_M_borel H.
  - exact: dgpr_main_M_rectifiable H.
  - exact: dgpr_main_M_finite H.
  - exact: htheta'.
  - exact: (@dgpr_density_product_summable R n k M theta htheta w hsum hHMw hw01M).
  - exact: dgpr_main_X_values H.
  - exact: hXm.
  - move=> g Dg hD.
    have [hPD hid] := hdec g Dg hD.
    have h1 := hconstr (P g) _ hPD.
    have h2 := real_total_integral_subtract hmu h1 (hJ g).
    have h2' : is_measure_integral mu (real_total_integrand (fun x => w x * HI (Xf x) (Dg x)))
        (- Ups (P g) - J g)%:E.
      suff <- : (fun x => HI (Xf x) (dgpr_rank_one (Dw x) (tv g x) + w x *: Dg x) - F g x) =
          (fun x => w x * HI (Xf x) (Dg x)) by exact: h2.
      by apply: funext => x; rewrite hid addrAC subrr add0r.
    have hmeas := dgpr_hom_pairing_measurable heY hHMm hXm (dgpr_test_differential_measurable hD).
    have h3 := dgpr_density_measure_change htheta hsum hHMw (fun x _ => hw0' x) hmeas h2'.
    have -> : - Ups' g = - Ups (P g) - J g by rewrite /Ups' hom_addE hom_compE opprD.
    exact: h3.
  - exact: hups'm.
  - exact: hups'r.
  - exact: hups'g.
  - by apply: le_lt_trans hups'B _; exact: ltry.
have hsupp : exists r0 : R, 0 < r0 /\
    measure_almost_everywhere (dgpr_main_measure k M theta') [set y | N y <= r0].
  exists (2 * r); split; first by rewrite mulr_gt0.
  rewrite /measure_almost_everywhere; apply: dgpr_density_measure_zero => x _ hx.
  rewrite /theta' hw0 ?mul0r //; apply: ltW; rewrite ltNge; apply/negP; exact: hx.
have hmain := hcc H' hsupp.
have hQ : 0 <= C * real_power (fine (HK M)) (k%:R)^-1.
  by rewrite mulr_ge0 // real_power_nonnegative.
apply: le_trans (@dgpr_density_measure_compare R n k M theta theta' [set y | N y < r] _ htheta') _.
  by move=> x hx hxr; rewrite /theta' hw1 ?mul1r // ltW.
apply: le_trans hmain _.
rewrite [X in (_ <= X)%E]EFinM; apply: lee_wpmul2l; first by rewrite lee_fin.
by apply: le_trans hups'B _; rewrite /Bd ha.
Qed.

(** Source for [dgpr_main_from_cutoff_bound]: blueprint proof of
    thm:main, the limit ϱ → ∞ in [dgpr_cutoff_bound]: since
    μ(U(0, j + 1)) increases to μ(R^n) (Federer 2.1.5(1)),
    μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n). Direct formalisation. *)
Lemma dgpr_main_from_cutoff_bound :
  (mu setT <= (C * real_power (fine (HK M)) (k%:R)^-1)%:E * ups setT)%E.
Proof.
have [c [hc hb]] := dgpr_cutoff_bound.
have [a ha] := dgpr_density_measure_finite htheta hsum.
have hupsm := dgpr_main_ups_measure H.
set u := fine (ups setT).
have hu : ups setT = u%:E.
  by rewrite /u fineK // ge0_fin_numE ?(measure_nonnegative hupsm) // (dgpr_main_ups_finite H).
have ha0 : 0 <= a by have := measure_nonnegative hmu setT; rewrite ha lee_fin.
have hLam := dgpr_main_Lambda H.
set Q := C * real_power (fine (HK M)) (k%:R)^-1.
have hQ : 0 <= Q by rewrite mulr_ge0 // real_power_nonnegative.
rewrite ha hu -EFinM lee_fin.
pose A (j : nat) := [set y : RnM | N y < j.+1%:R].
have hA (j : nat) : measure_measurable mu (A j).
  have h1 := open_borel_set (@dgpr_open_ball_open R n j.+1%:R).
  have h2 := dgpr_density_measure_borel k htheta h1.
  exact: h2.
have hinc (i j : nat) : (i <= j)%N -> A i `<=` A j.
  by move=> hij y; rewrite /A /= => h; apply: lt_le_trans h _; rewrite ler_nat ltnS.
have hU : \bigcup_j A j = setT.
  apply/seteqP; split=> // y _.
  exists (Num.bound (N y)) => //; rewrite /A /=.
  apply: lt_trans (archi_boundP (inner_norm_nonnegative BX y)) _.
  by rewrite ltr_nat.
have [_ hlim] := measure_continuity_below hmu hA hinc.
have hl : extended_order_limit (fun j => mu (A j)) a%:E by rewrite -ha -hU; exact: hlim.
rewrite leNgt; apply/negP => hlt.
set e := a - Q * u.
have he : 0 < e by rewrite subr_gt0.
have hlt0 : ((Q * u + e / 2)%:E < a%:E)%E by rewrite lte_fin /e; lra.
have [J1 hJ1] := hl.1 _ hlt0.
set D := Q * (c * Lam * a).
have hD0 : 0 <= D by rewrite mulr_ge0 // mulr_ge0 // mulr_ge0 // ltW.
set j := maxn J1 (Num.bound (2 * D / e)).
set s : R := j.+1%:R.
have hs : 0 < s by rewrite ltr0n.
have hDs : 2 * D / e < s.
  have hb0 : 0 <= 2 * D / e.
    by apply: divr_ge0; [apply: mulr_ge0 | exact: ltW].
  apply: lt_le_trans (archi_boundP hb0) _.
  by rewrite /s ler_nat; apply: leqW; exact: leq_maxr.
have hDs' : D / s < e / 2.
  rewrite ltr_pdivrMr // mulrAC.
  move: hDs; rewrite ltr_pdivrMr // [s * e]mulrC => hDs; lra.
have hj := hJ1 j (leq_maxl _ _).
have hbj := hb s hs.
rewrite ha /= in hbj.
have hlt' := lt_le_trans hj hbj.
rewrite lte_fin in hlt'.
have heq : Q * (u + c / s * Lam * a) = Q * u + D / s by rewrite /D; ring.
rewrite heq in hlt'.
move: hDs' hlt'; move: (D / s) (e / 2) (Q * u) => x y z; lra.
Qed.

End CutoffArgument.

Section MainFromCompact.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.

(** Source for [dgpr_main_from_compact_case]: blueprint thm:main and its
    proof: if 0 ≤ C and the conclusion of lem:compact_case holds for λ, Λ
    and C ([dgpr_compact_case_inequality]), then the conclusion of
    thm:main holds for λ, Λ and C ([dgpr_main_inequality]). Direct
    formalisation. *)
Theorem dgpr_main_from_compact_case (lam Lam C : R) : 0 <= C ->
  dgpr_compact_case_inequality hk lam Lam C -> dgpr_main_inequality hk lam Lam C.
Proof.
move=> hC hcc Y CY hCY d eY E ev hE K M theta Xf Ups ups H.
exact: (dgpr_main_from_cutoff_bound H hC hcc).
Qed.

(** Source for [dgpr_theorem_1_1_rectifiable]: DPGPR 2026, Theorem 1.1,
    for rectifiable data; blueprint thm:main: for 0 < λ and 0 < Λ, the
    constant C = [dgpr_compact_case_constant n C0] with
    C0 = [dgpr_upper_entropy_constant n λ Λ], which depends only on n, λ
    and Λ, satisfies μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n) for all data of
    mr:hypotheses_main. It combines lem:compact_case
    ([dgpr_compact_case_general], DgprCompactCaseGeneral.v) with
    [dgpr_main_from_compact_case]. *)
Theorem dgpr_theorem_1_1_rectifiable (lam Lam : R) : 0 < lam -> 0 < Lam ->
  dgpr_main_inequality hk lam Lam
    (dgpr_compact_case_constant n (dgpr_upper_entropy_constant n lam Lam)).
Proof.
move=> hlam hLam; apply: dgpr_main_from_compact_case.
  exact: ltW (dgpr_compact_case_constant_gt0 n _).
exact: dgpr_compact_case_general.
Qed.

End MainFromCompact.
