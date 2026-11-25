(** De Philippis, Gennaioli, Pigati and Rindler (2026), the Gaussian
    tube estimate in the proof of (4.2); blueprint lem:tube (section
    "Entropy"). Suppose 1 ≤ m ≤ n, E ⊆ R^n is compact and m rectifiable,
    H^m(E) > 0 and d(x) = dist(x, E) for x ∈ R^n. Then there is
    0 < s_0 ≤ 1 such that
      γ_s = ∫ exp(−d(x)^2/(4s)) dL^n x ≤ c(n) s^((n−m)/2) H^m(E)
    for 0 < s < s_0, where c(n) = 1 + 2 (4π)^(n/2).
    The blueprint writes γ_s by Fubini's theorem as an integral of
    L^n{x : d(x) < r} against a one-dimensional Gaussian weight. The
    formalisation uses a discrete form of this layer decomposition. With
    k = n − m, δ = (s/(2k + 1))^(1/2), ρ_j = jδ and φ_j = exp(−ρ_j^2/(4s)),
    the function [x ↦ exp(−d(x)^2/(4s))] is bounded by the layer sum
      Σ_(j<K) φ_j (1{d < ρ_(j+1)} − 1{d < ρ_j})
    on {x : d(x) < ρ_K} and by exp(−r_1^2/(128 s)) exp(−d(x)^2/8) on the
    rest. The integral of the layer sum is Σ_(j<K) φ_j (V_(j+1) − V_j),
    with V_j = L^n{x : d(x) < ρ_j} ≤ 2 α(k) ρ_j^k H^m(E) by the Minkowski
    content theorem (Federer 3.2.37, 3.2.39). Abel summation compares it
    with 2 H^m(E) times the same sum in R^k for the distance from {0},
    which is the integral of a layer sum over R^k and is bounded by the
    Gaussian integral of [y ↦ exp(1/4) exp(−(1 − ε)|y|^2/(4s))] with
    ε = (2k + 2)^(-1) (Federer 2.7.16, 3.2.13). The constants follow from
    1 + t ≤ exp(t) and exp(1/2) ≤ 2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra ring.
From Federer Require Import RealExponentialUP RealExponentialSealed
  EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology InnerNormInequalities
  MeasureUP MeasureBasic PartialFunctionBasic MeasureIntegralUP MeasureIntegralComparison
  SummableRealFunctionUP SummableRealArithmetic RealTotalCharacteristicBounds FunctionLatticeUP
  CharacteristicFunctionUP MeasureCharacteristicIntegral EuclideanLebesgueDimensions EuclideanBallVolume
  TopologicalBorel BorelRegularMeasureUP MetricSetDistanceUP MetricSetDistanceBasic
  MetricOpenThickening MetricOpenThickeningClosure NormClassOneUP NormOpenDomainLaws
  LatticeL1ApproximationLaws MinkowskiContents PositiveRadiusLimits ExtendedRealBounds
  ClosedRectifiableMinkowski RectifiableSetUP HausdorffMeasure CircularHalfPeriodLower
  CircularTrigonometrySealed.
From DPGPR Require Import DgprHeatKernel DgprLebesgueIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TubeScalars.
Variable R : realType.
Local Notation exp := (@RealExponential.exponential R).
Local Notation hexp := (@RealExponential.laws R).

(** Source for [dgpr_exp_gt0]: blueprint lem:tube, proof; the
    exponential of Federer 2.4.12 is positive (through the sealed
    exponential laws). Supporting lemma. *)
Lemma dgpr_exp_gt0 (x : R) : 0 < exp x.
Proof. exact: (real_exponential_positive hexp). Qed.

(** Source for [dgpr_exp_mono]: blueprint lem:tube, proof; the
    exponential is nondecreasing. Supporting lemma. *)
Lemma dgpr_exp_mono (x y : R) : x <= y -> exp x <= exp y.
Proof. exact: dgpr_exponential_le. Qed.

(** Source for [dgpr_exp_nonpos_le1]: blueprint lem:tube, proof;
    exp(x) ≤ 1 for x ≤ 0. Supporting lemma. *)
Lemma dgpr_exp_nonpos_le1 (x : R) : x <= 0 -> exp x <= 1.
Proof. by move=> hx; rewrite -(real_exponential_zero hexp); exact: dgpr_exp_mono. Qed.

(** Source for [dgpr_exp_inv]: blueprint lem:tube, proof;
    exp(−x) = exp(x)^(-1). Supporting lemma. *)
Lemma dgpr_exp_inv (x : R) : exp (- x) = (exp x)^-1.
Proof.
have h := real_exponential_add hexp x (- x).
rewrite subrr (real_exponential_zero hexp) in h.
by rewrite -[RHS]mul1r h mulrAC mulfV ?mul1r // gt_eqF // dgpr_exp_gt0.
Qed.

(** Source for [dgpr_exp_power]: blueprint lem:tube, proof;
    exp(x)^N = exp(N x) for every natural number N. Supporting lemma. *)
Lemma dgpr_exp_power (x : R) (N : nat) : exp x ^+ N = exp (N%:R * x).
Proof.
elim: N => [|N ih]; first by rewrite expr0 mul0r (real_exponential_zero hexp).
by rewrite exprS ih -(real_exponential_add hexp) -[N.+1]addn1 natrD mulrDl mul1r addrC.
Qed.

(** Source for [dgpr_exp_nonpos_lipschitz]: blueprint lem:tube, proof;
    |exp(x) − exp(y)| ≤ |x − y| for x ≤ 0 and y ≤ 0, used for the
    continuity, hence the L^n measurability, of
    [x ↦ exp(−d(x)^2/c)]. Supporting lemma. *)
Lemma dgpr_exp_nonpos_lipschitz (x y : R) : x <= 0 -> y <= 0 -> `|exp x - exp y| <= `|x - y|.
Proof.
wlog hxy : x y / y <= x.
  move=> hw hx hy; have [h|h] := boolP (y <= x).
    exact: (hw x y h hx hy).
  rewrite -ltNge in h.
  by rewrite distrC [`|x - y|]distrC; apply: (hw y x (ltW h) hy hx).
move=> hx hy.
have he : exp y = exp x * exp (y - x).
  by rewrite -(real_exponential_add hexp) addrCA subrr addr0.
have ht := real_exponential_tangent hexp (y - x).
have h1 := dgpr_exp_nonpos_le1 hx.
have h0 := dgpr_exp_gt0 x.
have hle : exp y <= exp x by exact: dgpr_exp_mono.
rewrite ger0_norm ?subr_ge0 // ger0_norm ?subr_ge0 // he.
have : exp x * (1 - exp (y - x)) <= 1 * (x - y).
  apply: ler_pM.
  - exact: ltW.
  - by rewrite subr_ge0; apply: dgpr_exp_nonpos_le1; rewrite subr_le0.
  - exact: h1.
  - lra.
by rewrite mul1r mulrBr mulr1.
Qed.

(** Source for [dgpr_exp_upper]: blueprint lem:tube, proof;
    exp(x) ≤ (1 − x)^(-1) for x < 1, from 1 − x ≤ exp(−x); used for
    exp(1/2) ≤ 2. Supporting lemma. *)
Lemma dgpr_exp_upper (x : R) : x < 1 -> exp x <= (1 - x)^-1.
Proof.
move=> hx; have ht := real_exponential_tangent hexp (- x).
rewrite dgpr_exp_inv in ht.
have hpos := dgpr_exp_gt0 x.
rewrite -(invrK (exp x)) lef_pV2 ?posrE ?invr_gt0 ?subr_gt0 //.
Qed.

(** Source for [dgpr_exp_decay]: blueprint lem:tube, proof, the decay
    of s^(−(n−m)/2) exp(−r_1^2/(8s)) as s → 0+, in the form
    exp(−a/s) ≤ ((N + 1) s/a)^(N+1) for 0 < a and 0 < s. Supporting
    lemma. *)
Lemma dgpr_exp_decay (a s : R) (N : nat) : 0 < a -> 0 < s ->
  exp (- (a / s)) <= (N.+1%:R * s / a) ^+ N.+1.
Proof.
move=> ha hs.
have hN : 0 < N.+1%:R :> R by rewrite ltr0n.
pose t := a / (N.+1%:R * s).
have ht : 0 < t by rewrite /t divr_gt0 // mulr_gt0.
have h1 : t <= exp t by have := real_exponential_tangent hexp t; lra.
have h2 : t ^+ N.+1 <= exp t ^+ N.+1.
  apply: lerXn2r => //; rewrite nnegrE ?ltW //; exact: dgpr_exp_gt0.
rewrite dgpr_exp_power in h2.
have e1 : N.+1%:R * t = a / s.
  rewrite /t; field.
  by rewrite gt_eqF //= addrC natr1 pnatr_eq0.
rewrite e1 in h2.
rewrite dgpr_exp_inv -(invrK ((N.+1%:R * s / a) ^+ N.+1)).
rewrite lef_pV2 ?posrE ?invr_gt0 ?exprn_gt0 ?divr_gt0 ?mulr_gt0 ?dgpr_exp_gt0 //.
rewrite -exprVn invf_div; exact: h2.
Qed.

(** Source for [dgpr_abel_le]: blueprint lem:tube, proof, the
    comparison of the layer integral with the bound for L^n(E_r), in
    discrete form (Abel summation). If V_j ≤ A W_j for j ≤ K,
    V_0 = W_0 = 0 and φ_K ≤ ... ≤ φ_0 with 0 ≤ φ_K, then
    Σ_(j<K) φ_j (V_(j+1) − V_j) ≤ A Σ_(j<K) φ_j (W_(j+1) − W_j).
    Supporting lemma. *)
Lemma dgpr_abel_le (K : nat) (phi V W : nat -> R) (A : R) :
  (forall j, (j <= K)%N -> V j <= A * W j) -> V 0%N = 0 -> W 0%N = 0 ->
  (forall j, (j < K)%N -> phi j.+1 <= phi j) -> 0 <= phi K ->
  \sum_(j < K) phi j * (V j.+1 - V j) <= A * \sum_(j < K) phi j * (W j.+1 - W j).
Proof.
move=> hVW hV0 hW0 hphi hK.
have abel (U : nat -> R) : U 0%N = 0 ->
    \sum_(j < K) phi j * (U j.+1 - U j) =
    \sum_(j < K) (phi j - phi j.+1) * U j.+1 + phi K * U K.
  move=> hU0; elim: K hVW hphi hK => [|K ih] _ _ _; first by rewrite !big_ord0 hU0 mulr0 addr0.
  rewrite !big_ord_recr /=.
  have ih' : \sum_(j < K) phi j * (U j.+1 - U j) =
      \sum_(j < K) (phi j - phi j.+1) * U j.+1 + phi K * U K.
    elim: K {ih} => [|K ihK]; first by rewrite !big_ord0 hU0 mulr0 addr0.
    rewrite !big_ord_recr /= ihK; ring.
  rewrite ih'; ring.
rewrite (abel V hV0) (abel W hW0) mulrDr mulr_sumr.
apply: lerD; last first.
  by rewrite mulrCA; apply: ler_wpM2l => //; exact: hVW.
apply: ler_sum => j _; rewrite mulrCA; apply: ler_wpM2l.
  by rewrite subr_ge0; exact: hphi.
exact: hVW.
Qed.

(** Source for [dgpr_shift_square]: blueprint lem:tube, proof, the
    comparison of a layer sum with a Gaussian:
    (1 − ε) t^2 − (ε^(-1) − 1) δ^2 ≤ a^2 whenever 0 < ε ≤ 1, 0 ≤ t,
    0 ≤ δ, 0 ≤ a and t − δ ≤ a. Supporting lemma. *)
Lemma dgpr_shift_square (e t d a : R) : 0 < e -> e <= 1 -> 0 <= t -> 0 <= d -> 0 <= a ->
  t - d <= a -> (1 - e) * t ^+ 2 - (e^-1 - 1) * d ^+ 2 <= a ^+ 2.
Proof.
move=> he he1 ht hd ha htd.
have hei : 1 <= e^-1 by rewrite invf_ge1.
have [hdt|hdt] := boolP (d <= t); last rewrite -ltNge in hdt.
- have h1 : (t - d) ^+ 2 <= a ^+ 2 by apply: lerXn2r; rewrite ?nnegrE ?subr_ge0.
  apply: le_trans h1.
  have hsq : 0 <= (e * t - d) ^+ 2 / e by rewrite divr_ge0 ?sqr_ge0 ?ltW.
  have hid : (t - d) ^+ 2 - ((1 - e) * t ^+ 2 - (e^-1 - 1) * d ^+ 2) = (e * t - d) ^+ 2 / e.
    by field; rewrite gt_eqF.
  by rewrite -subr_ge0 hid.
- have h1 : (1 - e) * t ^+ 2 <= (e^-1 - 1) * d ^+ 2.
    have hle : (1 - e) <= (e^-1 - 1).
      have -> : e^-1 - 1 = (1 - e) / e by field; rewrite gt_eqF.
      by rewrite ler_pdivlMr // ler_piMr ?subr_ge0.
    apply: ler_pM; rewrite ?subr_ge0 ?sqr_ge0 //.
    by apply: lerXn2r; rewrite ?nnegrE // ltW.
  by apply: le_trans (sqr_ge0 a); rewrite subr_le0.
Qed.

End TubeScalars.

Section Layers.
Variable R : realType.
Variables rho phi : nat -> R.
Hypothesis hrho : {homo rho : i j / (i <= j)%N >-> i <= j}.

(** Source for [dgpr_layer_sum]: blueprint lem:tube, proof, a discrete
    form of the layer decomposition (eq:tube:layer). For sequences ρ and
    φ, the layer sum at t is Σ_(j<K) φ_j (1{t < ρ_(j+1)} − 1{t < ρ_j}). *)
Definition dgpr_layer_sum (K : nat) (t : R) : R :=
  \sum_(j < K) phi j * (((t < rho j.+1)%R)%:R - ((t < rho j)%R)%:R).

(** Source for [dgpr_layer_sum_above]: blueprint lem:tube, proof; for a
    nondecreasing sequence ρ the layer sum vanishes at t ≥ ρ_K.
    Supporting lemma. *)
Lemma dgpr_layer_sum_above (K : nat) (t : R) : rho K <= t -> dgpr_layer_sum K t = 0.
Proof.
move=> hK; rewrite /dgpr_layer_sum big1 // => j _.
have h1 : rho j.+1 <= t := le_trans (hrho (ltn_ord j)) hK.
have h0 : rho j <= t := le_trans (hrho (leqnSn j)) h1.
by rewrite ltNge h1 ltNge h0 /= subrr mulr0.
Qed.

(** Source for [dgpr_layer_sum_upper]: blueprint lem:tube, proof; the
    layer sum at t is at most B ≥ 0 whenever φ_j ≤ B for every j < K
    with ρ_j ≤ t < ρ_(j+1). Supporting lemma. *)
Lemma dgpr_layer_sum_upper (K : nat) (t B : R) : 0 <= B ->
  (forall j, (j < K)%N -> rho j <= t -> t < rho j.+1 -> phi j <= B) ->
  dgpr_layer_sum K t <= B.
Proof.
move=> hB; elim: K => [|K ih] hphi; first by rewrite /dgpr_layer_sum big_ord0.
rewrite /dgpr_layer_sum big_ord_recr /= -/(dgpr_layer_sum K t).
have [htK|htK] := boolP (t < rho K).
  have htK1 : t < rho K.+1 := lt_le_trans htK (hrho (leqnSn K)).
  rewrite htK1 subrr mulr0 addr0; apply: ih => j hj; apply: hphi; exact: ltnW.
rewrite dgpr_layer_sum_above ?add0r; last by rewrite leNgt.
rewrite /= subr0; have [h|h] := boolP (t < rho K.+1); rewrite /= ?mulr1 ?mulr0 //.
by apply: hphi => //; rewrite leNgt.
Qed.

(** Source for [dgpr_layer_sum_lower]: blueprint lem:tube, proof; the
    layer sum at t with ρ_0 ≤ t < ρ_K is at least A whenever A ≤ φ_j for
    every j < K with ρ_j ≤ t < ρ_(j+1). Supporting lemma. *)
Lemma dgpr_layer_sum_lower (K : nat) (t A : R) : rho 0%N <= t -> t < rho K ->
  (forall j, (j < K)%N -> rho j <= t -> t < rho j.+1 -> A <= phi j) ->
  A <= dgpr_layer_sum K t.
Proof.
move=> h0; elim: K => [|K ih] htK hphi; first by move: (lt_le_trans htK h0); rewrite ltxx.
rewrite /dgpr_layer_sum big_ord_recr /= -/(dgpr_layer_sum K t).
have [htK'|htK'] := boolP (t < rho K).
  have htK1 : t < rho K.+1 := lt_le_trans htK' (hrho (leqnSn K)).
  rewrite htK1 subrr mulr0 addr0; apply: ih => // j hj; apply: hphi; exact: ltnW.
rewrite dgpr_layer_sum_above ?add0r; last by rewrite leNgt.
rewrite htK /= subr0 mulr1.
by apply: hphi => //; rewrite leNgt.
Qed.

End Layers.

Section LayerIntegral.
Variable R : realType.
Variable q : nat.
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R q)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R q)).
Local Notation LL := (@euclidean_lebesgue_measure R q).

(** Source for [dgpr_distance_sublevel_measurable]: blueprint lem:tube,
    proof; the set {y : u(y) < r} = E_r is open, since the distance
    function u of Federer 2.2.10 is continuous, hence L^q measurable
    (2.6.5, 2.1.4). Supporting lemma. *)
Lemma dgpr_distance_sublevel_measurable (A : set Y) (u : Y -> R) (r : R) :
  is_metric_set_distance A u -> measure_measurable LL [set y | u y < r].
Proof.
move=> hu; rewrite -(metric_open_thickening_distance r hu).
apply: (borel_regular_borel_measurable (euclidean_lebesgue_is_measure R q)
  (euclidean_lebesgue_borel_regular R q)).
apply: open_borel_set; exact: metric_open_thickening_open.
Qed.

(** Source for [dgpr_distance_sublevel0]: blueprint lem:tube, proof;
    {y : u(y) < 0} is empty for a distance function u. Supporting
    lemma. *)
Lemma dgpr_distance_sublevel0 (A : set Y) (u : Y -> R) :
  is_metric_set_distance A u -> LL [set y | u y < 0] = 0%E.
Proof.
move=> hu; rewrite (_ : [set y | u y < 0] = set0).
  exact: measure_empty (euclidean_lebesgue_is_measure R q).
apply/seteqP; split=> [y /= hy|y []].
by move: hy; rewrite ltNge (metric_set_distance_nonnegative hu y).
Qed.

(** Source for [dgpr_norm_distance]: blueprint lem:tube, proof; the norm
    of R^q is the distance from {0}. Supporting lemma. *)
Lemma dgpr_norm_distance : is_metric_set_distance [set (0 : Y)] NY.
Proof.
split.
- by move=> x a ->; rewrite inner_metric_distanceE subr0.
- by move=> x r hr; have := hr 0 erefl; rewrite inner_metric_distanceE subr0.
Qed.

(** Source for [dgpr_norm_sublevel]: blueprint lem:tube, proof;
    L^q{y : |y| < r} = α(q) r^q for 0 < r (Federer 2.7.16). Supporting
    lemma. *)
Lemma dgpr_norm_sublevel (r : R) : 0 < r ->
  LL [set y | NY y < r] = (euclidean_unit_ball_volume R q * r ^+ q)%:E.
Proof.
move=> hr; rewrite -(@euclidean_ball_measure R q 0 r hr).
by congr LL; apply/seteqP; split=> y /=; rewrite subr0 inner_norm_topologyE.
Qed.

(** Source for [dgpr_layer_integral]: blueprint lem:tube, proof,
    (eq:tube:layer) in discrete form: if u is the distance from a set in
    R^q and L^q{y : u(y) < ρ_j} < ∞ for j ≤ K, then the integral of
    [y ↦ layer sum at u(y)] with respect to L^q is
    Σ_(j<K) φ_j (L^q{u < ρ_(j+1)} − L^q{u < ρ_j}) (Federer 2.4.5,
    2.4.4). Supporting lemma. *)
Lemma dgpr_layer_integral (rho phi : nat -> R) (A : set Y) (u : Y -> R) (K : nat) :
  is_metric_set_distance A u ->
  (forall j, (j <= K)%N -> (LL [set y | (u y < rho j)%R] < +oo)%E) ->
  is_measure_integral LL (real_total_integrand (fun y => dgpr_layer_sum rho phi K (u y)))
    (\sum_(j < K) phi j * (fine (LL [set y | u y < rho j.+1]) - fine (LL [set y | u y < rho j])))%:E.
Proof.
move=> hu hfin.
have hm := euclidean_lebesgue_is_measure R q.
have hind j : (j <= K)%N -> is_measure_integral LL
    (real_total_integrand (fun y => (((u y < rho j)%R)%:R : R))) (fine (LL [set y | u y < rho j]))%:E.
  move=> hj.
  have hc : is_characteristic_function [set y | u y < rho j] (fun y => (((u y < rho j)%R)%:R : R)).
    split=> y /=; first by move=> ->.
    by move=> /negP /negbTE ->.
  have h := measure_characteristic_integral hm hc (dgpr_distance_sublevel_measurable (rho j) hu).
  rewrite fineK; first exact: h.
  rewrite ge0_fin_numE; [exact: hfin|exact: measure_nonnegative hm _].
have := @dgpr_real_integral_sum R Y LL 'I_K
  (fun j y => phi j * (((u y < rho j.+1)%R)%:R - ((u y < rho j)%R)%:R))
  (fun j => phi j * (fine (LL [set y | u y < rho j.+1]) - fine (LL [set y | u y < rho j]))) hm.
apply=> j; apply: (real_total_integral_scale hm).
apply: (real_total_integral_subtract hm).
- exact: hind (ltn_ord j).
- exact: hind (ltnW (ltn_ord j)).
Qed.

End LayerIntegral.

Section DistanceGaussian.
Variable R : realType.
Variable n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation exp := (@RealExponential.exponential R).

(** Source for [dgpr_distance_gaussian_class]: blueprint lem:tube; the
    function [x ↦ exp(−d(x)^2/c)] is continuous for the distance d from
    a set and 0 < c, because d is Lipschitzian with constant 1 (Federer
    2.2.10). Supporting lemma. *)
Lemma dgpr_distance_gaussian_class (A : set X) (d : X -> R) (c : R) :
  is_metric_set_distance A d -> 0 < c ->
  norm_class_zero N (fun t : R^o => `|t|) setT (fun x : X => exp (- d x ^+ 2 / c)).
Proof.
move=> hd hc a _; split; first exact: norm_full_domain_interior.
move=> e he; pose D := d a.
have hD : 0 <= D := metric_set_distance_nonnegative hd a.
have hD1 : 0 < 2 * D + 1 by rewrite ltr_pwDr // mulr_ge0.
exists (Num.min 1 (e * c / (2 * D + 1))); split.
  by rewrite lt_min ltr01 /= divr_gt0 // mulr_gt0.
move=> h _; rewrite lt_min => /andP [hh1 hh2].
pose x := d (a + h).
have hx : 0 <= x := metric_set_distance_nonnegative hd (a + h).
have hl : `|x - D| <= N h.
  have := metric_set_distance_lipschitz_one hd (a + h) a.
  by rewrite inner_metric_distanceE addrAC subrr add0r.
have e1 : - x ^+ 2 / c - - D ^+ 2 / c = (D - x) * (D + x) / c.
  by field; rewrite gt_eqF.
apply: (le_lt_trans (dgpr_exp_nonpos_lipschitz _ _)).
- by rewrite mulNr oppr_le0 divr_ge0 ?sqr_ge0 // ltW.
- by rewrite mulNr oppr_le0 divr_ge0 ?sqr_ge0 // ltW.
rewrite e1 normrM normfV (gtr0_norm hc) ltr_pdivrMr // normrM.
have hNh : 0 <= N h := inner_norm_nonnegative _ h.
have hsum : `|D + x| <= 2 * D + 1.
  rewrite ger0_norm ?addr_ge0 //.
  have : x - D <= N h by exact: le_trans (ler_norm _) hl.
  lra.
apply: (le_lt_trans (y := N h * (2 * D + 1))).
  by apply: ler_pM; rewrite ?normr_ge0 // distrC.
by rewrite -ltr_pdivlMr.
Qed.

(** Source for [dgpr_distance_gaussian_summable]: blueprint lem:tube,
    proof, the tail constant c_1: if |a| ≤ R_0 for a ∈ A, then
    d(x) ≥ |x| − R_0, d(x)^2 ≥ |x|^2/2 − R_0^2 and
    exp(−d(x)^2/c) ≤ exp(R_0^2/c) exp(−|x|^2/(2c)); hence
    [x ↦ exp(−d(x)^2/c)] is L^n summable (Federer 2.4.9, 3.2.13).
    Supporting lemma. *)
Lemma dgpr_distance_gaussian_summable (A : set X) (d : X -> R) (R0 c : R) :
  is_metric_set_distance A d -> (forall a, A a -> N a <= R0) -> 0 < c ->
  summable_real_functions LL (fun x : X => exp (- d x ^+ 2 / c)).
Proof.
move=> hd hR0 hc.
have hm := euclidean_lebesgue_is_measure R n.
pose R1 := Num.max R0 0.
have hR1 : 0 <= R1 by rewrite le_max lexx orbT.
have hc2 : 0 < 2 * c by rewrite mulr_gt0.
apply: (dgpr_dominated_summable (H := fun x : X => exp (R1 ^+ 2 / c) * exp (- N x ^+ 2 / (2 * c)))).
- exact: dgpr_continuous_measurable (dgpr_distance_gaussian_class hd hc).
- exact: (summable_real_scale hm _ (dgpr_gaussian_summable n hc2)).
move=> x; rewrite ger0_norm; last exact: ltW (dgpr_exp_gt0 _).
rewrite -(real_exponential_add (RealExponential.laws R)); apply: dgpr_exp_mono.
have ht : 0 <= N x := inner_norm_nonnegative _ x.
have hdx : 0 <= d x := metric_set_distance_nonnegative hd x.
have hgap : N x - R1 <= d x.
  apply: (metric_set_distance_greatest hd) => a ha.
  rewrite inner_metric_distanceE.
  have h1 := inner_norm_triangle (@euclidean_inner_productP R n) (x - a) a.
  rewrite subrK in h1.
  have h2 : N a <= R1 by rewrite le_max hR0.
  lra.
have hhalf : 0 < 2^-1 :> R by rewrite invr_gt0.
have hhalf1 : 2^-1 <= 1 :> R by rewrite invf_le1 // ler1n.
have key := dgpr_shift_square hhalf hhalf1 ht hR1 hdx hgap.
have e2 : 2^-1^-1 - 1 = 1 :> R by rewrite invrK; lra.
have e3 : 1 - 2^-1 = 2^-1 :> R by field.
rewrite e2 e3 mul1r in key.
have hq : 0 <= (d x ^+ 2 - (2^-1 * N x ^+ 2 - R1 ^+ 2)) / c.
  apply: divr_ge0; last exact: ltW.
  by rewrite subr_ge0.
have e4 : R1 ^+ 2 / c + - N x ^+ 2 / (2 * c) - - d x ^+ 2 / c =
    (d x ^+ 2 - (2^-1 * N x ^+ 2 - R1 ^+ 2)) / c by field; rewrite gt_eqF.
by rewrite -subr_ge0 e4.
Qed.

End DistanceGaussian.

Section LayerGaussian.
Variable R : realType.
Variable q : nat.
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R q)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R q)).
Local Notation LL := (@euclidean_lebesgue_measure R q).
Local Notation exp := (@RealExponential.exponential R).
Local Notation hexp := (@RealExponential.laws R).

(** Source for [dgpr_layer_gaussian_bound]: blueprint lem:tube, proof,
    the bound of the integral over (0, r_1) by 2 (4π)^(n/2) s^((n−m)/2)
    H^m(E), in R^q with q = n − m. For 0 < s, δ = (s/(2q + 1))^(1/2),
    ρ_j = jδ and φ_j = exp(−ρ_j^2/(4s)),
    Σ_(j<K) φ_j (L^q{|y| < ρ_(j+1)} − L^q{|y| < ρ_j}) ≤ 2 (4π)^(q/2) s^(q/2).
    The left side is the integral of the layer sum at |y|, which is at
    most exp(1/4) exp(−(1 − ε)|y|^2/(4s)) with ε = (2q + 2)^(-1); the
    integral of the latter is exp(1/4) (4πs/(1 − ε))^(q/2) (Federer
    3.2.13, 2.7.16), and exp(1/4) (1 − ε)^(−q/2) ≤ exp(1/2) ≤ 2. *)
Lemma dgpr_layer_gaussian_bound (s del : R) (rho phi : nat -> R) (K : nat) :
  0 < s -> del = Num.sqrt (s / (2 * q%:R + 1)) -> (forall j, rho j = j%:R * del) ->
  (forall j, phi j = exp (- rho j ^+ 2 / (4 * s))) ->
  \sum_(j < K) phi j * (fine (LL [set y | NY y < rho j.+1]) - fine (LL [set y | NY y < rho j]))
    <= 2 * Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q.
Proof.
move=> hs hdel hrhoE hphiE.
have hm := euclidean_lebesgue_is_measure R q.
pose qq : R := q%:R.
have hqq : 0 <= qq by rewrite /qq ler0n.
have hq1 : 0 < 2 * qq + 1 by rewrite ltr_pwDr // mulr_ge0.
have hdel0 : 0 < del by rewrite hdel sqrtr_gt0 divr_gt0.
have hrho : {homo rho : i j / (i <= j)%N >-> i <= j}.
  by move=> i j hij; rewrite !hrhoE; apply: ler_wpM2r; [exact: ltW|rewrite ler_nat].
have hrho0 j : 0 <= rho j by rewrite hrhoE mulr_ge0 ?ler0n ?ltW.
pose eps := (2 * qq + 2)^-1.
have heps : 0 < eps by rewrite /eps invr_gt0; lra.
have heps1 : eps <= 1 by rewrite /eps invf_le1; lra.
have heps2 : 0 < 1 - eps by rewrite subr_gt0 /eps invf_lt1; lra.
have hdel2 : (eps^-1 - 1) * del ^+ 2 = s.
  by rewrite /eps invrK hdel sqr_sqrtr ?divr_ge0 ?ltW //; field; rewrite gt_eqF.
pose edil := Num.sqrt (4 * s / (1 - eps)).
have hedil : 0 < edil by rewrite /edil sqrtr_gt0 divr_gt0 // mulr_gt0.
have hG := real_total_integral_scale hm (exp (4^-1))
  (dgpr_lebesgue_dilation hedil (dgpr_gaussian_integral R q)).
have hfin j : (LL [set y | (NY y < rho j)%R] < +oo)%E.
  case: j => [|j].
    rewrite hrhoE mul0r (dgpr_distance_sublevel0 (@dgpr_norm_distance R q)); exact: ltry.
  have hpos : 0 < rho j.+1 by rewrite hrhoE mulr_gt0 // ltr0n.
  rewrite (dgpr_norm_sublevel q hpos); exact: ltry.
have hIk := @dgpr_layer_integral R q rho phi _ _ K (@dgpr_norm_distance R q) (fun j _ => hfin j).
have hpt : function_le (fun y => dgpr_layer_sum rho phi K (NY y))
    (fun y => exp (4^-1) * exp (- NY (edil^-1 *: y) ^+ 2)).
  move=> y; apply: dgpr_layer_sum_upper => //.
    by rewrite mulr_ge0 // ltW // dgpr_exp_gt0.
  move=> j _ hlo hhi.
  rewrite hphiE -(real_exponential_add hexp); apply: dgpr_exp_mono.
  pose t := NY y.
  have ht : 0 <= t := inner_norm_nonnegative _ y.
  have en : NY (edil^-1 *: y) ^+ 2 = (1 - eps) * t ^+ 2 / (4 * s).
    rewrite inner_normZ gtr0_norm ?invr_gt0 // exprMn exprVn /edil sqr_sqrtr; last first.
      by rewrite divr_ge0 ?ltW // mulr_gt0.
    by rewrite /t; field; rewrite !gt_eqF.
  have hstep : t - del <= rho j.
    have e1 : rho j.+1 = rho j + del by rewrite !hrhoE -addn1 natrD mulrDl mul1r.
    rewrite e1 in hhi; rewrite /t; lra.
  have key := dgpr_shift_square heps heps1 ht (ltW hdel0) (hrho0 j) hstep.
  rewrite hdel2 in key.
  rewrite en -subr_ge0.
  have e2 : 4^-1 + - ((1 - eps) * t ^+ 2 / (4 * s)) - - rho j ^+ 2 / (4 * s) =
      (rho j ^+ 2 - ((1 - eps) * t ^+ 2 - s)) / (4 * s) by field; rewrite gt_eqF.
  by rewrite e2 divr_ge0 ?subr_ge0 // ltW // mulr_gt0.
have hmono := measure_integral_monotone hm hIk hG (real_total_pointwise_order_almost hm hpt).
rewrite lee_fin in hmono; apply: (le_trans hmono).
pose w := Num.sqrt ((1 - eps)^-1).
have hw : 0 <= w := sqrtr_ge0 _.
have epi : edil ^+ q * Num.sqrt (dgpr_pi R) ^+ q =
    Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q * w ^+ q.
  rewrite -!exprMn; congr (_ ^+ q).
  have h4s : 0 <= 4 * s / (1 - eps) by rewrite divr_ge0 ?ltW // mulr_gt0.
  have h4p : 0 <= 4 * dgpr_pi R by rewrite mulr_ge0 // ltW // dgpr_pi_gt0.
  have h4ps : 0 <= 4 * dgpr_pi R * s by rewrite mulr_ge0 // ltW.
  rewrite /edil /w -(sqrtrM _ h4s) -(sqrtrM _ h4p) -(sqrtrM _ h4ps).
  by congr Num.sqrt; field; rewrite gt_eqF.
rewrite epi mulrCA [_ * w ^+ q]mulrC mulrA.
have hpi : 0 <= Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q.
  by rewrite mulr_ge0 // exprn_ge0 // sqrtr_ge0.
have hwq : w ^+ q <= exp (4^-1).
  have hA : w ^+ q \is Num.nneg by rewrite nnegrE exprn_ge0.
  have hB : exp (4^-1) \is Num.nneg by rewrite nnegrE ltW // dgpr_exp_gt0.
  rewrite -(@ler_pXn2r R 2 erefl _ _ hA hB).
  rewrite -exprM mulnC exprM /w sqr_sqrtr; last by rewrite invr_ge0; exact: ltW heps2.
  rewrite dgpr_exp_power.
  have e3 : (1 - eps)^-1 = 1 + (2 * qq + 1)^-1 by rewrite /eps; field; rewrite !gt_eqF //; lra.
  have h1 : (1 - eps)^-1 <= exp ((2 * qq + 1)^-1).
    by rewrite e3; exact: real_exponential_tangent hexp _.
  have h2 : ((1 - eps)^-1) ^+ q <= exp ((2 * qq + 1)^-1) ^+ q.
    apply: lerXn2r => //; rewrite nnegrE ?invr_ge0 ?ltW //; exact: dgpr_exp_gt0.
  apply: (le_trans h2); rewrite dgpr_exp_power; apply: dgpr_exp_mono.
  rewrite -/qq; apply: (@le_trans _ _ (2^-1)).
    by rewrite ler_pdivrMr //; lra.
  have e6 : (2 : R) / 4 = 2^-1 by field.
  by rewrite e6.
have hfin2 : w ^+ q * exp (4^-1) <= 2.
  apply: (le_trans (ler_wpM2r (ltW (dgpr_exp_gt0 _)) hwq)).
  rewrite -(real_exponential_add hexp).
  have e4 : 4^-1 + 4^-1 = 2^-1 :> R by field.
  rewrite e4; apply: (le_trans (dgpr_exp_upper _)); first lra.
  have e5 : (1 - 2^-1)^-1 = 2 :> R by field.
  by rewrite e5.
have -> : 2 * Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q =
    (Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q) * 2 by ring.
have -> : Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q * w ^+ q * exp 4^-1 =
    (Num.sqrt (4 * dgpr_pi R) ^+ q * Num.sqrt s ^+ q) * (w ^+ q * exp 4^-1) by ring.
by apply: ler_wpM2l.
Qed.

End LayerGaussian.

Section TubeEstimate.
Variable R : realType.
Variables n m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation HH := (@hausdorff_measure R X m).
Local Notation exp := (@RealExponential.exponential R).

(** Source for [dgpr_tube_minkowski]: blueprint lem:tube, proof, second
    paragraph: since E is closed and m rectifiable, the upper Minkowski
    content of E equals H^m(E) (Federer 3.2.37, 3.2.39); hence, if
    0 < H^m(E) < ∞, there is 0 < e with
    L^n{x : d(x) < r} < 2 H^m(E) α(n − m) r^(n−m) for 0 < r < e. *)
Lemma dgpr_tube_minkowski (E : set X) (d : X -> R) (h : R) :
  (m <= n)%N -> compact E -> is_m_rectifiable m E -> is_metric_set_distance E d ->
  HH E = h%:E -> 0 < h ->
  exists e : R, 0 < e /\ forall r, 0 < r < e ->
    (LL [set x | (d x < r)%R] <
      (2 * h * (euclidean_unit_ball_volume R (n - m) * r ^+ (n - m)))%:E)%E.
Proof.
move=> hmn hE hEr hd hh hpos.
have hcl : closed E := compact_closed (@metric_hausdorff R X) hE.
have [hup _] := closed_rectifiable_minkowski_equalities hmn hcl hEr.
rewrite hh /upper_minkowski_content /positive_radius_upper_limit in hup.
have [e [he hb]] : exists e : R, 0 < e /\ (extended_real_sup
    (positive_radius_values (minkowski_tube_quotient m E) e) < (2 * h)%:E)%E.
  apply: contrapT => hno.
  have : ((2 * h)%:E <= h%:E)%E.
    rewrite -hup; apply: extended_real_inf_greatest => b [e [he ->]].
    rewrite leNgt; apply/negP => hlt; apply: hno; by exists e.
  rewrite lee_fin; lra.
exists e; split => // r /andP [hr hre].
have hq : 0 < euclidean_unit_ball_volume R (n - m) * r ^+ (n - m).
  by rewrite mulr_gt0 ?exprn_gt0 // (@euclidean_unit_ball_volumeE R (n - m)).2.
have hfr : (minkowski_tube_quotient m E r <=
    extended_real_sup (positive_radius_values (minkowski_tube_quotient m E) e))%E.
  by apply: extended_real_sup_upper; exists r; split => //; rewrite hr hre.
have := le_lt_trans hfr hb.
rewrite /minkowski_tube_quotient inver (gt_eqF hq) lte_pdivrMr // -EFinM.
by rewrite (metric_open_thickening_distance r hd).
Qed.

(** Source for [dgpr_compact_norm_bound]: blueprint lem:tube, proof,
    "choose 0 < R_0 < ∞ with E ⊆ B(0, R_0)". Supporting lemma. *)
Lemma dgpr_compact_norm_bound (E : set X) : compact E -> exists R0 : R, forall a, E a -> N a <= R0.
Proof.
move=> hE; have [M [_ hM]] := compact_bounded hE.
exists (M + 1) => a ha.
have hlt : M < M + 1 by rewrite ltrDl ltr01.
have h := hM (M + 1) hlt.
rewrite -inner_norm_topologyE; exact: h a ha.
Qed.

(** Source for [dgpr_tube_summable]: blueprint lem:tube, the definition
    of γ_s: for compact E and 0 < s the function
    [x ↦ exp(−dist(x, E)^2/(4s))] is L^n summable. *)
Lemma dgpr_tube_summable (E : set X) (d : X -> R) (s : R) :
  compact E -> is_metric_set_distance E d -> 0 < s ->
  summable_real_functions LL (fun x : X => exp (- d x ^+ 2 / (4 * s))).
Proof.
move=> hE hd hs; have [R0 hR0] := dgpr_compact_norm_bound hE.
by apply: (dgpr_distance_gaussian_summable hd hR0); rewrite mulr_gt0.
Qed.

(** Source for [dgpr_tube_estimate]: DPGPR 2026, proof of (4.2);
    blueprint lem:tube. Here d is the distance function of E
    (is_metric_set_distance, Federer 2.2.10), the integral γ_s is any g
    with [is_measure_integral], which exists by [dgpr_tube_summable], and
    the bound is stated in the extended real numbers. The proof is the
    discrete layer argument described at the head of this file: with
    r_1 = min{e, 1} for the e of [dgpr_tube_minkowski], a = r_1^2/128,
    c_1 the integral of [x ↦ exp(−d(x)^2/8)] and
    s_0 = min{1, r_1^2/16, H^m(E)/(c_1 ((k + 1)/a)^(k+1) + 1)},
    γ_s ≤ 2 H^m(E) · 2 (4π)^(k/2) s^(k/2) + exp(−a/s) c_1
        ≤ 2 (4π)^(n/2) s^(k/2) H^m(E) + s^(k/2) H^m(E)
    for 0 < s < s_0, where k = n − m and 1 ≤ m. *)
Theorem dgpr_tube_estimate (E : set X) (d : X -> R) :
  (0 < m)%N -> (m <= n)%N -> compact E -> is_m_rectifiable m E -> (0 < HH E)%E ->
  is_metric_set_distance E d ->
  exists s0 : R, 0 < s0 <= 1 /\ forall s : R, 0 < s < s0 -> forall g : R,
    is_measure_integral LL (real_total_integrand (fun x : X => exp (- d x ^+ 2 / (4 * s)))) g%:E ->
    (g%:E <= ((1 + 2 * Num.sqrt (4 * dgpr_pi R) ^+ n) * Num.sqrt s ^+ (n - m))%:E * HH E)%E.
Proof.
move=> hm0 hmn hE hEr hEpos hd.
have hm := euclidean_lebesgue_is_measure R n.
have hHm := hausdorff_measure_is_measure X m.
set k := (n - m)%N.
have hpi : 3 <= dgpr_pi R by rewrite /dgpr_pi; exact: (@circular_half_period_at_least_three R).
have hsq4 : 2 <= Num.sqrt (4 * dgpr_pi R).
  have hA : (2 : R) \is Num.nneg by rewrite nnegrE.
  have hB : Num.sqrt (4 * dgpr_pi R) \is Num.nneg by rewrite nnegrE sqrtr_ge0.
  rewrite -(@ler_pXn2r R 2 erefl _ _ hA hB) sqr_sqrtr; last by rewrite mulr_ge0 //; lra.
  lra.
pose c0 := 1 + 2 * Num.sqrt (4 * dgpr_pi R) ^+ n.
have hc0 : 0 < c0 by rewrite /c0 ltr_pwDl // mulr_ge0 // exprn_ge0 // sqrtr_ge0.
case hHE : (HH E) => [h| |]; last first.
- by have := measure_nonnegative hHm E; rewrite hHE.
- exists 1; split; first by rewrite ltr01 lexx.
  move=> s /andP [hs _] g _.
  have hp : 0 < c0 * Num.sqrt s ^+ k by rewrite mulr_gt0 // exprn_gt0 // sqrtr_gt0.
  by rewrite mulry gtr0_sg // mul1e leey.
have hh : 0 < h by rewrite hHE lte_fin in hEpos.
have [e [he hmink]] := dgpr_tube_minkowski hmn hE hEr hd hHE hh.
have [R0 hR0] := dgpr_compact_norm_bound hE.
have h8 : (0 : R) < 8 by [].
have [c1 hc1] := dgpr_distance_gaussian_summable hd hR0 h8.
have hc1pos : 0 <= c1.
  have hz := real_total_zero_integral hm.
  have hle : function_le (fun _ : X => 0 : R) (fun x : X => exp (- d x ^+ 2 / 8)).
    by move=> x; exact: ltW (dgpr_exp_gt0 _).
  have := measure_integral_monotone hm hz hc1 (real_total_pointwise_order_almost hm hle).
  by rewrite lee_fin.
pose r1 := Num.min e 1.
have hr1 : 0 < r1 by rewrite lt_min he ltr01.
have hr1e : r1 <= e by rewrite ge_min lexx.
have hr11 : r1 <= 1 by rewrite ge_min lexx orbT.
pose a := r1 ^+ 2 / 128.
have ha : 0 < a by rewrite divr_gt0 // exprn_gt0.
pose C2 := c1 * (k.+1%:R / a) ^+ k.+1.
have hC2 : 0 <= C2 by rewrite mulr_ge0 // exprn_ge0 // divr_ge0 // ltW.
pose s0 := Num.min 1 (Num.min (r1 ^+ 2 / 16) (h / (C2 + 1))).
exists s0; split.
  rewrite lt_min ltr01 lt_min divr_gt0 ?exprn_gt0 //= ?ge_min ?lexx //.
  by rewrite divr_gt0 //; lra.
move=> s /andP [hs]; rewrite !lt_min => /and3P [hs1 hsr hsh] g hg.
pose kk : R := k%:R.
have hkk : 0 <= kk by rewrite /kk ler0n.
pose del := Num.sqrt (s / (2 * kk + 1)).
pose rho := fun j : nat => j%:R * del.
pose phi := fun j : nat => exp (- rho j ^+ 2 / (4 * s)).
have hdel : 0 < del by rewrite sqrtr_gt0 divr_gt0 //; lra.
have hdels : del <= Num.sqrt s.
  rewrite ler_sqrt; last exact: ltW.
  rewrite ler_pdivrMr; last lra.
  have hs0 := ltW hs; nra.
have hsqs : Num.sqrt s < r1 / 4.
  have e1 : r1 ^+ 2 / 16 = (r1 / 4) ^+ 2 by field.
  have := hsr; rewrite e1 -(ltr_sqrt) ?exprn_gt0 ?divr_gt0 // sqrtr_sqr gtr0_norm //.
  by rewrite divr_gt0.
pose K := Num.truncn (r1 / (2 * del)).
have hq0 : 0 <= r1 / (2 * del) by rewrite divr_ge0 ?ltW // mulr_gt0.
have hK1 : K%:R * del <= r1 / 2.
  have := truncn_le (r1 / (2 * del)); rewrite hq0 -/K => hK.
  have : K%:R * (2 * del) <= r1 by rewrite -ler_pdivlMr // mulr_gt0.
  lra.
have hK2 : r1 / 2 < K.+1%:R * del.
  have := truncn_le_nat (r1 / (2 * del)) K; rewrite leqnn -/K => /esym hK.
  have : r1 < K.+1%:R * (2 * del) by rewrite -ltr_pdivrMr // mulr_gt0.
  lra.
have hrhoK1 : r1 / 4 <= rho K.
  have e1 : K.+1%:R * del = K%:R * del + del by rewrite -natr1 mulrDl mul1r.
  rewrite e1 in hK2; rewrite /rho; lra.
have hrhoKe : rho K < e by rewrite /rho; lra.
have hrho : {homo rho : i j / (i <= j)%N >-> i <= j}.
  by move=> i j hij; rewrite /rho; apply: ler_wpM2r; [exact: ltW|rewrite ler_nat].
have hrho0 j : 0 <= rho j by rewrite /rho mulr_ge0 // ltW.
have hrhoe j : (j <= K)%N -> rho j < e by move=> hj; exact: le_lt_trans (hrho _ _ hj) hrhoKe.
have hpos j : 0 < rho j.+1 by rewrite /rho mulr_gt0 // ltr0n.
have hfinn j : (j <= K)%N -> (LL [set x | (d x < rho j)%R] < +oo)%E.
  case: j => [|j] hj.
    by rewrite /rho mul0r (dgpr_distance_sublevel0 hd) ltry.
  have hr : 0 < rho j.+1 < e by rewrite hpos hrhoe.
  exact: lt_trans (hmink _ hr) (ltry _).
have hIn := @dgpr_layer_integral R n rho phi E d K hd hfinn.
have hSk := @dgpr_layer_gaussian_bound R k s del rho phi K hs erefl (fun j => erefl) (fun j => erefl).
pose V := fun j : nat => fine (LL [set x | (d x < rho j)%R]).
pose W := fun j : nat => fine (@euclidean_lebesgue_measure R k
  [set y | (inner_norm (@euclidean_inner_productP R k) y < rho j)%R]).
have hVW j : (j <= K)%N -> V j <= 2 * h * W j.
  case: j => [|j] hj.
    rewrite /V /W /rho mul0r (dgpr_distance_sublevel0 hd).
    by rewrite (dgpr_distance_sublevel0 (@dgpr_norm_distance R k)) /= mulr0.
  have hr : 0 < rho j.+1 < e by rewrite hpos hrhoe.
  have hlt := hmink _ hr.
  have hf : LL [set x | (d x < rho j.+1)%R] \is a fin_num.
    by rewrite ge0_fin_numE ?(measure_nonnegative hm) // (lt_trans hlt (ltry _)).
  rewrite /W (dgpr_norm_sublevel k (hpos j)) /= -lee_fin /V fineK //.
  exact: ltW hlt.
have hV0 : V 0%N = 0 by rewrite /V /rho mul0r (dgpr_distance_sublevel0 hd).
have hW0 : W 0%N = 0 by rewrite /W /rho mul0r (dgpr_distance_sublevel0 (@dgpr_norm_distance R k)).
have hphid j : (j < K)%N -> phi j.+1 <= phi j.
  move=> _; apply: dgpr_exp_mono; rewrite !mulNr lerN2 ler_pM2r ?invr_gt0 ?mulr_gt0 //.
  by apply: lerXn2r; rewrite ?nnegrE ?hrho0 // hrho.
have hphiK : 0 <= phi K by exact: ltW (dgpr_exp_gt0 _).
have hAbel : \sum_(j < K) phi j * (fine (LL [set x | (d x < rho j.+1)%R]) -
    fine (LL [set x | (d x < rho j)%R])) <=
    2 * h * \sum_(j < K) phi j * (fine (@euclidean_lebesgue_measure R k
      [set y | (inner_norm (@euclidean_inner_productP R k) y < rho j.+1)%R]) -
      fine (@euclidean_lebesgue_measure R k
      [set y | (inner_norm (@euclidean_inner_productP R k) y < rho j)%R])).
  exact: (@dgpr_abel_le R K phi V W (2 * h) hVW hV0 hW0 hphid hphiK).
have hpt : function_le (fun x : X => exp (- d x ^+ 2 / (4 * s)))
    (fun x : X => dgpr_layer_sum rho phi K (d x) + exp (- (a / s)) * exp (- d x ^+ 2 / 8)).
  move=> x; pose D := d x.
  have hD : 0 <= D := metric_set_distance_nonnegative hd x.
  have hT : 0 <= exp (- (a / s)) * exp (- D ^+ 2 / 8).
    by rewrite mulr_ge0 // ltW // dgpr_exp_gt0.
  have [hDK|hDK] := boolP (D < rho K).
    have hl : exp (- D ^+ 2 / (4 * s)) <= dgpr_layer_sum rho phi K D.
      apply: (dgpr_layer_sum_lower hrho) => //; first by rewrite /rho mul0r.
      move=> j _ hlo _; apply: dgpr_exp_mono.
      rewrite !mulNr lerN2 ler_pM2r ?invr_gt0 ?mulr_gt0 //.
      by apply: lerXn2r; rewrite ?nnegrE ?hrho0.
    rewrite -/D; lra.
  rewrite -leNgt in hDK.
  rewrite -/D (dgpr_layer_sum_above phi hrho hDK) add0r -(real_exponential_add (RealExponential.laws R)).
  apply: dgpr_exp_mono.
  have hD2 : r1 ^+ 2 / 16 <= D ^+ 2.
    have e1 : r1 ^+ 2 / 16 = (r1 / 4) ^+ 2 by field.
    rewrite e1; apply: lerXn2r.
    - by rewrite nnegrE divr_ge0 // ltW.
    - by rewrite nnegrE.
    - exact: le_trans hrhoK1 hDK.
  have hDs : D ^+ 2 * s <= D ^+ 2 by rewrite ler_piMr ?sqr_ge0 // ltW.
  have e2 : - (a / s) + - D ^+ 2 / 8 - - D ^+ 2 / (4 * s) =
      (2 * D ^+ 2 - r1 ^+ 2 / 16 - D ^+ 2 * s) / (8 * s).
    by rewrite /a; field; rewrite gt_eqF.
  rewrite -subr_ge0 e2; apply: divr_ge0; first lra.
  by rewrite mulr_ge0 // ltW.
have hR := real_total_integral_add hm hIn (real_total_integral_scale hm (exp (- (a / s))) hc1).
have hmono := measure_integral_monotone hm hg hR (real_total_pointwise_order_almost hm hpt).
rewrite lee_fin in hmono.
have hsk1 : Num.sqrt s ^+ k <= 1.
  apply: exprn_ile1; first exact: sqrtr_ge0.
  by rewrite -sqrtr1 ler_sqrt //; exact: ltW.
have hsk0 : 0 <= Num.sqrt s ^+ k by rewrite exprn_ge0 // sqrtr_ge0.
have hsk : s ^+ k <= Num.sqrt s ^+ k.
  rewrite -{1}(sqr_sqrtr (ltW hs)) -exprM mulnC exprM expr2.
  exact: ler_piMr.
have htail : exp (- (a / s)) * c1 <= h * Num.sqrt s ^+ k.
  have h1 : exp (- (a / s)) * c1 <= (k.+1%:R * s / a) ^+ k.+1 * c1.
    have hdec := dgpr_exp_decay k ha hs.
    by apply: ler_wpM2r.
  have e1 : (k.+1%:R * s / a) ^+ k.+1 * c1 = C2 * s * s ^+ k.
    rewrite /C2 (_ : k.+1%:R * s / a = k.+1%:R / a * s); last by rewrite mulrAC.
    rewrite exprMn [s ^+ k.+1]exprS; set P := (k.+1%:R / a) ^+ k.+1; set Q := s ^+ k.
    ring.
  have hC2s : C2 * s <= h.
    have : s * (C2 + 1) < h by rewrite -ltr_pdivlMr //; lra.
    have : 0 <= s by exact: ltW.
    nra.
  apply: (le_trans h1); rewrite e1.
  apply: (le_trans (ler_wpM2l _ hsk)); first by rewrite mulr_ge0 // ltW.
  by apply: ler_wpM2r.
have hpow : 2 * Num.sqrt (4 * dgpr_pi R) ^+ k <= Num.sqrt (4 * dgpr_pi R) ^+ n.
  have -> : n = (k + m)%N by rewrite /k subnK.
  rewrite exprD mulrC; apply: ler_wpM2l; first by rewrite exprn_ge0 // sqrtr_ge0.
  apply: (le_trans hsq4); apply: ler_eXnr => //; lra.
rewrite -EFinM lee_fin; apply: (le_trans hmono).
have e3 : c0 * Num.sqrt s ^+ k * h =
    2 * h * (Num.sqrt (4 * dgpr_pi R) ^+ n * Num.sqrt s ^+ k) + h * Num.sqrt s ^+ k.
  by rewrite /c0; ring.
rewrite e3; apply: lerD; last exact: htail.
apply: (le_trans hAbel); apply: ler_wpM2l; first by rewrite mulr_ge0 // ltW.
apply: (le_trans hSk); by apply: ler_wpM2r.
Qed.

End TubeEstimate.
