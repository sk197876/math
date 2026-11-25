(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3; blueprint
    dgpr_blueprint.tex, lem:heat_extension(1) and (2) for every j. For
    0 < s the map u_s is of class infinity on R^n; for every multi-index
    alpha, D^alpha u_s(x) is the integral of D^alpha p_s(x-y) f(y) d nu y
    (the multi-index derivatives of Federer 3.1.11, p. 223, which determine
    D^j u_s(x)); and ||D^j u_s(x)|| <= c s^(-j/2) (1 + (|x| + r) s^(-1/2))^j
    times the integral of p_s(x-y) |f(y)| d nu y. The proofs differentiate
    under the integral sign along coordinate directions, using the graded
    family of DgprHeatKernelHigher.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerNormInequalities
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureVectorIntegralUP
  SummableRealFunctionUP SummableRealArithmetic CompleteMetricUP VectorDaniellHypotheses
  MeasurableFunctionUP MeasureAlmostUP MeasureAlmostBasic TotalVectorIntegralAlmostDominatedNorm
  NormDifferentialUP NormClassOneUP NormClassZeroArithmetic NormClassZeroScalarProduct
  NormRegularity NormClassHigherUP NormedCurveDerivativeUP NormPartialDerivative
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricExponentWords
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherMultiPartialUP
  NormIteratedDirectionalUP NormIteratedDirectionalLaws MultiPartialOrderedIdentification
  HigherDifferentialFinitePartialBound RealCurveDerivativeUP
  ScalarNormMetricCompleteness RealExponentialUP RealExponentialSealed CircularTrigonometrySealed.
From DPGPR Require Import DgprGrowthClasses DgprParameterIntegralDifferential DgprParameterIntegralSmooth
  DgprHeatKernel DgprHeatKernelDifferential DgprHeatExtension DgprHeatKernelFamily DgprHeatExtensionSmooth
  DgprHeatExtensionBounds DgprHeatKernelHigher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Translation.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation A1 := (fun t : R^o => `|t|).

(** Source for [dgpr_translate_class_zero]: continuity of [x |-> k(x-y)];
    lem:heat_extension(1), proof. *)
Lemma dgpr_translate_class_zero (k : X -> R) (y : X) :
  norm_class_zero N A1 setT k -> norm_class_zero N A1 setT (fun x => k (x - y)).
Proof.
move=> hk a _; split; first exact: dgpr_interior_setT.
move=> e he; have [_ hc] := hk (a - y) I; have [d [hd hd']] := hc e he.
exists d; split => // h _ hh.
have e1 : a + h - y = a - y + h by rewrite addrAC.
by rewrite e1; apply: hd'.
Qed.
End Translation.

Section HeatHigher.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation e := (@coordinate_basis R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Variable Z : lmodType R.
Variable NZ : Z -> R.
Hypothesis hNZ : is_real_norm NZ.
Hypothesis hZ : is_complete_metric_space (real_norm_metric_space hNZ).
Variable f : X -> Z.
Hypothesis hOpen : forall A : set X, @open (real_norm_metric_space hN) A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Hypothesis hsep : is_separable_normed_space hNZ.
Hypothesis hfmeas : is_measure_measurable_function nu
  (partial_function_total (fun y => (f y : real_norm_metric_space hNZ))).
Variable M : R.
Hypothesis hfM : forall y, NZ (f y) <= M.
Local Notation conv := (@dgpr_convolution R n nu hnu Z NZ hNZ hZ f).
Local Notation u := (@dgpr_heat_extension R n nu hnu Z NZ hNZ hZ f).
Local Notation has_integral := (@dgpr_has_integral R X nu Z NZ hNZ).
Local Notation ez := (fun j => @ContinuousMultilinear.evaluation R j X Z N NZ hN hNZ).
Local Notation ZN := (fun j => @ContinuousMultilinear.norm R j X Z N NZ hN hNZ).
Local Notation ep := (fun j => @ContinuousMultilinear.evaluation R j X R^o N A1 hN hA).
Local Notation PN := (fun j => @ContinuousMultilinear.norm R j X R^o N A1 hN hA).

(** Source for [dgpr_graded_partial_space]: the partial derivative in x
    of [x |-> q(s,x-y) f(y)]; lem:heat_extension(1), proof. *)
Lemma dgpr_graded_partial_space (q qi : R -> X -> R) (s : R) (y : X) (i : 'I_n) :
  (forall z, has_real_curve_derivative (fun t => q s (z + t *: e i)) 0 (qi s z)) ->
  forall x, has_norm_partial_derivative NZ (fun x' => q s (x' - y) *: f y) x i (qi s (x - y) *: f y).
Proof.
move=> hqi x.
have hl := dgpr_scalar_vector_limit hNZ (f y) (hqi (x - y)).
rewrite /has_norm_partial_derivative.
apply: (dgpr_punctured_congr _ hl) => t /=.
by rewrite scale0r addr0 addrAC.
Qed.

(** Source for [dgpr_graded_domination]: for fixed 0 < s the integrands
    [y |-> q(s,x-y) f(y)] are bounded by a constant, which is nu summable;
    lem:heat_extension(1), proof. *)
Lemma dgpr_graded_domination (d : nat) (q : R -> X -> R) (s : R) : dgpr_kernel_graded d q -> 0 < s ->
  forall x, exists (r : R) (g : X -> R), 0 < r /\ summable_real_functions nu g /\
    forall h y, N h < r -> setT (x + h) -> NZ (q s (x + h - y) *: f y) <= g y.
Proof.
move=> hq hs x.
have [C hC] := dgpr_family_uniform_bound (dgpr_kernel_graded_family hq) s hs.
exists 1, (fun _ => C * M); split => //; split.
  exact: (dgpr_constant_summable hnu hmass (C * M)).
move=> h y _ _.
rewrite (real_seminorm_scale hNZ.1); apply: ler_pM.
- exact: normr_ge0.
- exact: (real_seminorm_nonnegative hNZ.1).
- exact: (hC s _ (lexx s) (lexx s)).
- exact: hfM.
Qed.

(** Source for [dgpr_heat_extension_space_smooth]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(1): for 0 < s the map u_s is of class
    infinity on R^n. *)
Theorem dgpr_heat_extension_space_smooth (s : R) : 0 < s -> norm_class_all_orders hN hNZ setT (u s).
Proof.
move=> hs.
pose K := fun k : X -> X -> Z =>
  exists d q, @dgpr_kernel_graded R n d q /\ k = (fun x y => q s (x - y) *: f y).
have h1 : forall x, setT x -> norm_domain_interior N setT x by move=> x _; exact: dgpr_interior_setT.
have h2 : forall k, K k -> forall x, setT x -> exists z, has_integral (k x) z.
  move=> k [d [q [hq ->]]] x _; exists (conv (q s) x).
  exact: (dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
    (dgpr_kernel_graded_family hq) hs).
have h3 : forall k, K k -> forall y, norm_class_zero N NZ setT (fun x => k x y).
  move=> k [d [q [hq ->]]] y.
  exact: (norm_class_zero_scalar_product hNZ
    (dgpr_translate_class_zero y (dgpr_kernel_family_class_zero (dgpr_kernel_graded_family hq) hs))
    (norm_class_zero_constant hNZ (f y) h1)).
have h4 : forall k, K k -> forall i, exists k', K k' /\
    forall x y, setT x -> has_norm_partial_derivative NZ (fun w => k w y) x i (k' x y).
  move=> k [d [q [hq ->]]] i.
  have [qi [hqi hqi']] := dgpr_kernel_graded_space_derivative hq i.
  exists (fun x y => qi s (x - y) *: f y); split; first by exists d.+1, qi.
  by move=> x y _; exact: (dgpr_graded_partial_space y (fun z => hqi' s z hs) x).
have h5 : forall k, K k -> forall x, setT x -> exists (r : R) (g : X -> R), 0 < r /\
    summable_real_functions nu g /\ forall h y, N h < r -> setT (x + h) -> NZ (k (x + h) y) <= g y.
  by move=> k [d [q [hq ->]]] x _; exact: (dgpr_graded_domination hq hs).
have hK : K (fun x y => p s (x - y) *: f y) by exists 0%N, p; split => //; exact: dgpr_kernel_graded_base.
exact: (@dgpr_parameter_integral_smooth R X nu hnu n Z NZ hNZ setT K h1 h2 h3 h4 h5 _ _ hK
  (fun x _ => dgpr_heat_extension_integral hnu hZ hOpen hmass hsep hfmeas hfM x hs)).
Qed.

(** Source for [dgpr_heat_extension_iterated]: for every sequence
    i_1, ..., i_k of coordinates there is a member q of degree k of the
    graded family such that, for 0 < s, q_s is the iterated directional
    derivative of p_s along e_(i_1), ..., e_(i_k), and the convolution of
    q_s with f nu is that of u_s (Federer 3.1.11, p. 223);
    lem:heat_extension(1), proof. *)
Lemma dgpr_heat_extension_iterated (nus : seq 'I_n) : exists q, dgpr_kernel_graded (size nus) q /\
  (forall s z, 0 < s -> has_norm_iterated_directional A1 setT (p s) [seq e i | i <- nus] z (q s z)) /\
  (forall s x, 0 < s -> has_norm_iterated_directional NZ setT (u s) [seq e i | i <- nus] x (conv (q s) x)).
Proof.
elim: nus => [|i nus [q0 [hq0 [hk0 hu0]]]].
  exists p; split; first exact: dgpr_kernel_graded_base.
  by split => s z hs.
have [q1 [hq1 hd]] := dgpr_kernel_graded_space_derivative hq0 i.
exists q1; split => //; split => s z hs /=.
  exists (q0 s); split.
    move=> x w hw; exact: (norm_iterated_directional_unique hA (hk0 s x hs) hw).
  split.
    exists 1; split; first exact: ltr01.
    by move=> t _; exists (q0 s (z + t *: e i)); exact: hk0.
  exact: (dgpr_curve_partial (hd s z hs)).
exists (conv (q0 s)); split.
  move=> x w hw; exact: (norm_iterated_directional_unique hNZ (hu0 s x hs) hw).
split.
  exists 1; split; first exact: ltr01.
  by move=> t _; exists (conv (q0 s) (z + t *: e i)); exact: hu0.
have hI0 x : has_integral (fun y => q0 s (x - y) *: f y) (conv (q0 s) x).
  exact: (dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
    (dgpr_kernel_graded_family hq0) hs).
have hI1 : has_integral (fun y => q1 s (z - y) *: f y) (conv (q1 s) z).
  exact: (dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM z
    (dgpr_kernel_graded_family hq1) hs).
exact: (@dgpr_parameter_integral_partial R X nu hnu n Z NZ hNZ setT
  (fun x y => q0 s (x - y) *: f y) (fun x y => q1 s (x - y) *: f y) (conv (q0 s)) (conv (q1 s)) z i
  I (dgpr_interior_setT z) (fun x _ => hI0 x) hI1
  (fun x y _ => dgpr_graded_partial_space y (fun w => hd s w hs) x)
  (dgpr_graded_domination hq1 hs z)).
Qed.

(** Source for [dgpr_heat_extension_multi_partial]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(1) for every j: for 0 < s, a multi-index
    alpha of degree k and x in R^n, D^alpha u_s(x) is the integral of
    D^alpha p_s(x-y) f(y) d nu y, where D^alpha is the multi-index
    derivative of Federer 3.1.11, p. 223. *)
Theorem dgpr_heat_extension_multi_partial (s : R) (k : nat) (alpha : symmetric_indices n k) (x : X)
    (theta : X -> R) : 0 < s ->
  (forall z, has_norm_multi_partial N ep PN setT (p s) alpha z (theta z)) ->
  has_norm_multi_partial N ez ZN setT (u s) alpha x (conv theta x).
Proof.
move=> hs htheta.
pose nus := symmetric_monomial_word idfun (symmetric_indices_unbound alpha).
have hSize : size nus = k by rewrite /nus symmetric_monomial_word_size symmetric_indices_unbound_degree.
have hCount i : count_mem i nus = symmetric_indices_unbound alpha i.
  have h := congr1 (fun a : symmetric_multi_index n => a i)
    (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
  by rewrite /symmetric_exponent_word_count ffunE in h.
have [q [_ [hk hu]]] := dgpr_heat_extension_iterated nus.
have -> : theta = q s.
  apply: funext => z.
  have hIt := @norm_multi_partial_to_ordered R n R^o A1 hA
    (fun j => @ContinuousMultilinear.space R j X R^o N A1 hN hA) ep PN
    (fun j => @ContinuousMultilinear.laws R j X R^o N A1 hN hA) setT (p s) k alpha nus z _
    hSize hCount (htheta z).
  exact: (norm_iterated_directional_unique hA hIt (hk s z hs)).
have [_ [D [hD _]]] := dgpr_heat_extension_space_smooth hs k.
exists (D x); split; first exact: (hD x I).
have hMP : has_norm_multi_partial N ez ZN setT (u s) alpha x
    (@ContinuousMultilinear.evaluation R k X Z N NZ hN hNZ (norm_multi_partial_arguments R alpha) (D x)).
  by exists (D x); split => //; exact: (hD x I).
have hIt := @norm_multi_partial_to_ordered R n Z NZ hNZ
  (fun j => @ContinuousMultilinear.space R j X Z N NZ hN hNZ) ez ZN
  (fun j => @ContinuousMultilinear.laws R j X Z N NZ hN hNZ) setT (u s) k alpha nus x _
  hSize hCount hMP.
exact: (norm_iterated_directional_unique hNZ hIt (hu s x hs)).
Qed.

Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].
Hypothesis hr : 0 <= r.

(** Source for [dgpr_graded_heat_bound]: for a member q of degree d,
    |int q_s(x-y) f(y) d nu y| <= C s^(-d/2) (1 + (|x| + r) s^(-1/2))^d
    times the integral of p_s(x-y) |f(y)| d nu y; blueprint
    lem:heat_extension(2), proof. *)
Lemma dgpr_graded_heat_bound (d : nat) (q : R -> X -> R) (C : R) : dgpr_kernel_graded d q -> 0 <= C ->
  (forall s z, 0 < s -> `|q s z| <= C * (Num.sqrt s)^-1 ^+ d * (1 + N z / Num.sqrt s) ^+ d * p s z) ->
  forall s x, 0 < s -> NZ (conv (q s) x) <=
    C * (Num.sqrt s)^-1 ^+ d * (1 + (N x + r) / Num.sqrt s) ^+ d * dgpr_heat_norm_extension hnu NZ f s x.
Proof.
move=> hq hC hb s x hs.
have hI : has_integral (fun y => q s (x - y) *: f y) (conv (q s) x).
  exact: (dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
    (dgpr_kernel_graded_family hq) hs).
set K := C * (Num.sqrt s)^-1 ^+ d * (1 + (N x + r) / Num.sqrt s) ^+ d.
have hG := real_total_integral_scale hnu K (dgpr_heat_norm_integral hnu hOpen hmass hfmeas hfM x hs).
apply: (total_vector_integral_almost_dominated_norm hnu hI hG).
apply: (measure_almost_everywhere_mono hnu _ hsupp) => y hy /=.
have hw : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hP := dgpr_kernel_gt0 (x - y) hs.
have hf0 := real_seminorm_nonnegative hNZ.1 (f y).
have hxy0 := inner_norm_nonnegative (@euclidean_inner_productP R n) (x - y).
rewrite (real_seminorm_scale hNZ.1).
apply: le_trans (ler_wpM2r hf0 (hb s (x - y) hs)) _.
have hd : 1 + N (x - y) / Num.sqrt s <= 1 + (N x + r) / Num.sqrt s.
  by rewrite lerD2l ler_pM2r ?invr_gt0 //; exact: dgpr_distance_upper.
have ha0 : 0 <= 1 + N (x - y) / Num.sqrt s by rewrite addr_ge0 // divr_ge0 // ltW.
have hc0 : 0 <= (Num.sqrt s)^-1 by rewrite invr_ge0 ltW.
rewrite /K; move: hd ha0; move: (1 + N (x - y) / Num.sqrt s) (1 + (N x + r) / Num.sqrt s) => a b hab ha0.
move: (p s (x - y)) hP => P hP; move: ((Num.sqrt s)^-1 ^+ d) (exprn_ge0 d hc0) => c hc.
have hpow : a ^+ d <= b ^+ d by rewrite lerXn2r // ?nnegrE // (le_trans ha0 hab).
have -> : C * c * a ^+ d * P * NZ (f y) = (C * c * P * NZ (f y)) * a ^+ d by ring.
have -> : C * c * b ^+ d * (P * NZ (f y)) = (C * c * P * NZ (f y)) * b ^+ d by ring.
by apply: ler_wpM2l => //; rewrite !mulr_ge0 // ltW.
Qed.

(** Source for [dgpr_heat_extension_higher_bound]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(2) for every j: there is 0 < c < oo with
    ||D^j u_s(x)|| <= c s^(-j/2) (1 + (|x| + r) s^(-1/2))^j times the
    integral of p_s(x-y) |f(y)| d nu y, for 0 < s and x in R^n, where
    D^j u_s(x) is the jth differential of Federer 3.1.11 and ||.|| its
    norm (p. 219). *)
Theorem dgpr_heat_extension_higher_bound (k : nat) : exists c : R, 0 < c /\
  forall (s : R) (x : X) (D : @ContinuousMultilinear.space R k X Z N NZ hN hNZ), 0 < s ->
    dgpr_higher_differential hN hNZ setT (u s) k x D ->
    @ContinuousMultilinear.norm R k X Z N NZ hN hNZ D <=
      c * (Num.sqrt s)^-1 ^+ k * (1 + (N x + r) / Num.sqrt s) ^+ k * dgpr_heat_norm_extension hnu NZ f s x.
Proof.
have [M0 [hM0 hMb]] := @norm_higher_differential_finite_partial_bound R n Z NZ hNZ
  (fun j => @ContinuousMultilinear.space R j X Z N NZ hN hNZ) ez ZN
  (fun j => @ContinuousMultilinear.laws R j X Z N NZ hN hNZ) k.
have hT : forall t : k.-tuple 'I_n, exists C : R, 0 <= C /\ forall s x, 0 < s -> exists y : Z,
    has_norm_iterated_directional NZ setT (u s) [seq e i | i <- t] x y /\
    NZ y <= C * (Num.sqrt s)^-1 ^+ k * (1 + (N x + r) / Num.sqrt s) ^+ k * dgpr_heat_norm_extension hnu NZ f s x.
  move=> t; have [q [hq [_ hu]]] := dgpr_heat_extension_iterated t.
  rewrite size_tuple in hq.
  have [C [hC hb]] := dgpr_kernel_graded_bound hq.
  exists C; split => // s x hs; exists (conv (q s) x); split; first exact: hu.
  exact: (dgpr_graded_heat_bound hq hC hb x hs).
have [Cf hCf] := choice hT.
pose Cs := \sum_(t : k.-tuple 'I_n) Cf t.
have hCt t : Cf t <= Cs.
  rewrite /Cs (bigD1 t) //= lerDl; apply: sumr_ge0 => t' _; exact: (hCf t').1.
have hCs : 0 <= Cs by apply: sumr_ge0 => t _; exact: (hCf t).1.
exists (M0 * (Cs + 1)); split.
  by apply: mulr_gt0 => //; apply: lt_le_trans ltr01 _; rewrite lerDr.
move=> s x D hs hD.
have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hNx := inner_norm_nonnegative (@euclidean_inner_productP R n) x.
have hU0 : 0 <= dgpr_heat_norm_extension hnu NZ f s x.
  apply: le_trans (dgpr_heat_extension_zero_bound hnu hZ hOpen hmass hsep hfmeas hfM x hs).
  exact: (real_seminorm_nonnegative hNZ.1).
have hW : 0 <= (Num.sqrt s)^-1 ^+ k * (1 + (N x + r) / Num.sqrt s) ^+ k * dgpr_heat_norm_extension hnu NZ f s x.
  have hqi : 0 <= (Num.sqrt s)^-1 by rewrite invr_ge0 ltW.
  have hb0 : 0 <= 1 + (N x + r) / Num.sqrt s by rewrite addr_ge0 // mulr_ge0 // addr_ge0.
  by rewrite !mulr_ge0 // exprn_ge0.
have hr0 : 0 <= Cs * ((Num.sqrt s)^-1 ^+ k * (1 + (N x + r) / Num.sqrt s) ^+ k *
  dgpr_heat_norm_extension hnu NZ f s x) by rewrite mulr_ge0.
have halpha : forall alpha : symmetric_indices n k,
    NZ (@ContinuousMultilinear.evaluation R k X Z N NZ hN hNZ (norm_multi_partial_arguments R alpha) D) <=
      Cs * ((Num.sqrt s)^-1 ^+ k * (1 + (N x + r) / Num.sqrt s) ^+ k * dgpr_heat_norm_extension hnu NZ f s x).
  move=> alpha.
  pose nus := symmetric_monomial_word idfun (symmetric_indices_unbound alpha).
  have hSize : size nus = k by rewrite /nus symmetric_monomial_word_size symmetric_indices_unbound_degree.
  have hCount i : count_mem i nus = symmetric_indices_unbound alpha i.
    have h := congr1 (fun a : symmetric_multi_index n => a i)
      (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
    by rewrite /symmetric_exponent_word_count ffunE in h.
  have hMP : has_norm_multi_partial N ez ZN setT (u s) alpha x
      (@ContinuousMultilinear.evaluation R k X Z N NZ hN hNZ (norm_multi_partial_arguments R alpha) D).
    by exists D.
  have hIt := @norm_multi_partial_to_ordered R n Z NZ hNZ
    (fun j => @ContinuousMultilinear.space R j X Z N NZ hN hNZ) ez ZN
    (fun j => @ContinuousMultilinear.laws R j X Z N NZ hN hNZ) setT (u s) k alpha nus x _
    hSize hCount hMP.
  have hS : size nus == k by rewrite hSize.
  have [_ hb] := hCf (Tuple hS).
  have [y [hy hyb]] := hb s x hs.
  rewrite (norm_iterated_directional_unique hNZ hIt hy).
  move: hyb hW; move: (dgpr_heat_norm_extension hnu NZ f s x) ((Num.sqrt s)^-1 ^+ k)
    ((1 + (N x + r) / Num.sqrt s) ^+ k) => Uz a1 a2 hyb hW.
  apply: le_trans hyb _.
  rewrite -!mulrA; apply: ler_wpM2r; [by rewrite mulrA | exact: hCt].
have hDM := hMb setT (u s) x D _ hr0 hD halpha.
move: hDM hW; move: (dgpr_heat_norm_extension hnu NZ f s x) ((Num.sqrt s)^-1 ^+ k)
  ((1 + (N x + r) / Num.sqrt s) ^+ k) => Uz a1 a2 hDM hW.
apply: le_trans hDM _.
have -> : M0 * (Cs + 1) * a1 * a2 * Uz = M0 * ((Cs + 1) * (a1 * a2 * Uz)) by ring.
apply: ler_wpM2l; first exact: ltW.
by apply: ler_wpM2r => //; rewrite lerDl.
Qed.

End HeatHigher.
