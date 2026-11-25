(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3; blueprint
    dgpr_blueprint.tex, lem:heat_extension(1): the heat extension u of
    (nu,f) is of class infinity on (0,infinity) x R^n, and
    d/ds u(s,x) = Delta u_s(x). The proof differentiates under the integral
    sign (DgprParameterIntegralSmooth.v) the integrands
    [(s,x) |-> q(s,x-y) f(y)] for the members q of the kernel family of
    DgprHeatKernelFamily.v, first on R^(n+1) with coordinate 0 as time,
    then on R x R^n with the product inner product of Federer 1.7.11, the
    space used in def:classes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerNormInequalities PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureVectorIntegralUP SummableRealFunctionUP CompleteMetricUP VectorDaniellHypotheses
  MeasurableFunctionUP NormDifferentialUP NormClassOneUP NormClassZeroArithmetic NormClassZeroScalarProduct
  NormOpenDomainLaws NormPartialDerivative NormedCurveDerivativeUP NormedCurveLinearMap NormedCurveChainRule
  NormedCurveParameterTranslation RealCurveDerivativeUP NormRegularity NormRegularityOperations
  NormRegularityLinearMaps InnerProductUP ProductInner ScalarInnerProduct ProductInnerNormBounds
  TotalVectorIntegralFiniteSum FiniteCoordinates CoordinateProjection EuclideanCoordinateMetric
  RealExponentialUP RealExponentialSealed.
From DPGPR Require Import DgprParameterIntegralDifferential DgprParameterIntegralSmooth DgprHeatKernel
  DgprHeatKernelDifferential DgprHeatExtension DgprHeatKernelFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dgpr_scale_one]: t 1 = t in R; bookkeeping for
    lem:heat_extension(1). *)
Lemma dgpr_scale_one (R : realType) (t : R) : t *: (1 : R^o) = t.
Proof. exact: mulr1. Qed.

(** Source for [dgpr_real_curve_translate]: translation of the parameter
    of a real curve, Federer 2.9.19, p. 163; blueprint
    lem:heat_extension(1). *)
Lemma dgpr_real_curve_translate (R : realType) (phi : R -> R) (s t v : R) :
  has_real_curve_derivative phi (s + t) v -> has_real_curve_derivative (fun r => phi (s + r)) t v.
Proof.
rewrite /has_real_curve_derivative.
have -> : (fun h => (phi (s + (t + h)) - phi (s + t)) / h) = (fun h => (phi (s + t + h) - phi (s + t)) / h).
  by apply: funext => h; rewrite addrA.
by [].
Qed.

Section HeatSmooth.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R n.+1).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation H := (@dgpr_positive_time R n).
Local Notation sp := (@dgpr_space_part R n).
Local Notation e := (@coordinate_basis R n).
Local Notation eW := (@coordinate_basis R n.+1).
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
Local Notation has_integral := (@dgpr_has_integral R X nu Z NZ hNZ).
Local Notation conv := (@dgpr_convolution R n nu hnu Z NZ hNZ hZ f).
Local Notation u := (@dgpr_heat_extension R n nu hnu Z NZ hNZ hZ f).

(** Source for [dgpr_family_uniform_bound]: every member of the kernel
    family is bounded on each strip a <= s <= b with 0 < a;
    lem:heat_extension(1), proof. *)
Lemma dgpr_family_uniform_bound (q : R -> X -> R) : dgpr_kernel_family q ->
  forall a b : R, 0 < a -> exists C : R, forall s z, a <= s -> s <= b -> `|q s z| <= C.
Proof.
move=> hq a b ha; have [C hC] := dgpr_kernel_family_bound hq a b ha 0.
by exists C => s z h1 h2; have := hC s z h1 h2; rewrite expr0 mul1r.
Qed.

(** Source for [dgpr_family_convolution_integral]: for a member q of the
    kernel family and 0 < s the function [y |-> q(s,x-y) f(y)] is nu
    summable with integral the convolution; def:heat and
    lem:heat_extension(1). *)
Lemma dgpr_family_convolution_integral (q : R -> X -> R) (s : R) (x : X) :
  dgpr_kernel_family q -> 0 < s -> has_integral (fun y => q s (x - y) *: f y) (conv (q s) x).
Proof.
move=> hq hs; have [C hC] := dgpr_family_uniform_bound hq s hs.
exact: (dgpr_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
  (dgpr_kernel_family_class_zero hq hs) (fun z => hC s z (lexx s) (lexx s))).
Qed.

(** Source for [dgpr_punctured_congr]: limits depend only on the values;
    bookkeeping for lem:heat_extension(1). *)
Lemma dgpr_punctured_congr (g g' : R -> Z) (v : Z) :
  (forall h, g h = g' h) -> punctured_norm_limit NZ g' v -> punctured_norm_limit NZ g v.
Proof. by move=> hg; have -> : g = g' by apply: funext. Qed.

(** Source for [dgpr_scalar_vector_limit]: if phi has the derivative v at
    0, then [t |-> phi(t) c] has the derivative v c at 0 (Federer 2.9.22,
    3.1.1); lem:heat_extension(1). *)
Lemma dgpr_scalar_vector_limit (phi : R -> R) (c : Z) (v : R) :
  has_real_curve_derivative phi 0 v ->
  punctured_norm_limit NZ (fun t => t^-1 *: (phi t *: c - phi 0 *: c)) (v *: c).
Proof.
move=> hphi.
have hn := (scalar_normed_curve_derivative phi 0 v).2 hphi.
have hb : norm_bounded_linear A1 NZ (dgpr_line_hom c).
  exists (NZ c); split; first exact: (real_seminorm_nonnegative hNZ.1).
  by move=> h; rewrite dgpr_line_homE (real_seminorm_scale hNZ.1) mulrC.
have hl := punctured_norm_limit_bounded_linear hA hb hn.
rewrite dgpr_line_homE in hl.
apply: (dgpr_punctured_congr _ hl) => h.
rewrite dgpr_line_homE add0r -scalerBl scalerA; reflexivity.
Qed.

(** Source for [dgpr_family_partial_space]: the partial derivative in the
    coordinate lift(0,i) of R^(n+1), a space direction, of
    [(s,x) |-> q(s,x-y) f(y)]; lem:heat_extension(1), proof. *)
Lemma dgpr_family_partial_space (q qi : R -> X -> R) (y : X) (i : 'I_n) :
  (forall s z, 0 < s -> has_real_curve_derivative (fun t => q s (z + t *: e i)) 0 (qi s z)) ->
  forall w, H w -> has_norm_partial_derivative NZ (fun w' : W => q (w' ord0) (sp w' - y) *: f y)
    w (lift ord0 i) (qi (w ord0) (sp w - y) *: f y).
Proof.
move=> hqi w hw.
have e1 (t : R) : (w + t *: eW (lift ord0 i)) ord0 = w ord0.
  by rewrite !ffunE (negbTE (neq_lift ord0 i)) scaler0 addr0.
have e2 (t : R) : sp (w + t *: eW (lift ord0 i)) - y = (sp w - y) + t *: e i.
  apply/ffunP => k; rewrite !ffunE (inj_eq (@lift_inj _ ord0)).
  by rewrite addrAC.
rewrite /has_norm_partial_derivative.
apply: (dgpr_punctured_congr _ (dgpr_scalar_vector_limit (f y) (hqi (w ord0) (sp w - y) hw))) => t /=.
by rewrite e1 e2 scale0r addr0.
Qed.

(** Source for [dgpr_family_partial_time]: the partial derivative in the
    coordinate 0 of R^(n+1), the time direction, of
    [(s,x) |-> q(s,x-y) f(y)]; lem:heat_extension(1), proof. *)
Lemma dgpr_family_partial_time (q qt : R -> X -> R) (y : X) :
  (forall s z, 0 < s -> has_real_curve_derivative (fun t => q t z) s (qt s z)) ->
  forall w, H w -> has_norm_partial_derivative NZ (fun w' : W => q (w' ord0) (sp w' - y) *: f y)
    w ord0 (qt (w ord0) (sp w - y) *: f y).
Proof.
move=> hqt w hw.
have e1 (t : R) : (w + t *: eW ord0) ord0 = w ord0 + t.
  by rewrite !ffunE eqxx dgpr_scale_one.
have e2 (t : R) : sp (w + t *: eW ord0) = sp w.
  apply/ffunP => k; rewrite !ffunE eq_sym (negbTE (neq_lift ord0 k)).
  by rewrite scaler0 addr0.
have hd := (dgpr_real_curve_shift _ _ _).1 (hqt (w ord0) (sp w - y) hw).
rewrite /has_norm_partial_derivative.
apply: (dgpr_punctured_congr _ (dgpr_scalar_vector_limit (f y) hd)) => t /=.
by rewrite e1 e2 addr0.
Qed.

(** Source for [dgpr_family_domination]: the integrands are dominated near
    each point of (0,infinity) x R^n by a constant, which is nu summable;
    lem:heat_extension(1), proof. *)
Lemma dgpr_family_domination (q : R -> X -> R) : dgpr_kernel_family q ->
  forall w, H w -> exists (r : R) (g : X -> R), 0 < r /\ summable_real_functions nu g /\
    forall h y, NW h < r -> H (w + h) -> NZ (q ((w + h) ord0) (sp (w + h) - y) *: f y) <= g y.
Proof.
move=> hq w hw; have hw0 : 0 < w ord0 := hw.
have ha : 0 < w ord0 / 2 by rewrite divr_gt0.
have [C hC] := dgpr_family_uniform_bound hq (2 * w ord0) ha.
exists (w ord0 / 2), (fun _ => C * M); split => //; split.
  exact: (dgpr_constant_summable hnu hmass (C * M)).
move=> h y hh _.
have hc := @dgpr_coordinate_abs_le R n.+1 h ord0.
have hn1 := ler_norm (h ord0); have hn2 := ler_norm (- h ord0); rewrite normrN in hn2.
have e1 : (w + h) ord0 = w ord0 + h ord0 by rewrite ffunE.
have hb := hC ((w + h) ord0) (sp (w + h) - y).
rewrite (real_seminorm_scale hNZ.1); apply: ler_pM.
- exact: normr_ge0.
- exact: (real_seminorm_nonnegative hNZ.1).
- by apply: hb; rewrite e1; lra.
- exact: hfM.
Qed.

(** Source for [dgpr_heat_extension_class_coordinates]: DPGPR 2026,
    section 3; blueprint lem:heat_extension(1), class infinity: the map
    [(s,x) |-> u(s,x)], written on R^(n+1) with coordinate 0 as time, is
    of class infinity on the half space 0 < s. *)
Theorem dgpr_heat_extension_class_coordinates :
  norm_class_all_orders hNW hNZ H (fun w : W => u (w ord0) (sp w)).
Proof.
pose K := fun k : W -> X -> Z =>
  exists q, @dgpr_kernel_family R n q /\ k = (fun w y => q (w ord0) (sp w - y) *: f y).
have h1 : forall w, H w -> norm_domain_interior NW H w := @dgpr_positive_time_interior R n.
have h2 : forall k, K k -> forall w, H w -> exists z, has_integral (k w) z.
  move=> k [q [hq ->]] w hw; exists (conv (q (w ord0)) (sp w)).
  exact: dgpr_family_convolution_integral.
have h3 : forall k, K k -> forall y, norm_class_zero NW NZ H (fun w => k w y).
  move=> k [q [hq ->]] y.
  exact: (norm_class_zero_scalar_product hNZ (dgpr_kernel_family_joint_class_zero hq y)
    (norm_class_zero_constant hNZ (f y) h1)).
have h4 : forall k, K k -> forall j, exists k', K k' /\
    forall w y, H w -> has_norm_partial_derivative NZ (fun w' => k w' y) w j (k' w y).
  move=> k [q [hq ->]] j.
  case: (unliftP ord0 j) => [i ->|->].
  - have [qi [hqi hqi']] := dgpr_kernel_family_space_derivative hq i.
    exists (fun (w : W) (y : X) => qi (w ord0) (sp w - y) *: f y); split; first by exists qi.
    by move=> w y hw; exact: dgpr_family_partial_space.
  - have [qt [hqt hqt']] := dgpr_kernel_family_time_derivative hq.
    exists (fun (w : W) (y : X) => qt (w ord0) (sp w - y) *: f y); split; first by exists qt.
    by move=> w y hw; exact: dgpr_family_partial_time.
have h5 : forall k, K k -> forall w, H w -> exists (r : R) (g : X -> R), 0 < r /\
    summable_real_functions nu g /\ forall h y, NW h < r -> H (w + h) -> NZ (k (w + h) y) <= g y.
  by move=> k [q [hq ->]] w hw; exact: dgpr_family_domination.
have hK : K (fun w y => p (w ord0) (sp w - y) *: f y) by exists p; split => //; exact: dgpr_kernel_family_base.
exact: (@dgpr_parameter_integral_smooth R X nu hnu n.+1 Z NZ hNZ H K h1 h2 h3 h4 h5 _ _ hK
  (fun w hw => dgpr_heat_extension_integral hnu hZ hOpen hmass hsep hfmeas hfM (sp w) hw)).
Qed.
End HeatSmooth.

Section ProductSpace.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R n.+1).
Local Notation NW := (inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation sp := (@dgpr_space_part R n).

(** Source for [dgpr_time_space_map]: the identification of R x R^n with
    R^(n+1), the time becoming coordinate 0; supporting def:classes and
    lem:heat_extension(1). *)
Definition dgpr_time_space_map (q : TX) : W :=
  [ffun j => if unlift ord0 j is Some i then q.2 i else q.1].

(** Source for [dgpr_time_space_linear]: the identification is linear;
    supporting lem:heat_extension(1). *)
Lemma dgpr_time_space_linear : linear dgpr_time_space_map.
Proof.
move=> c a b; apply/ffunP => j; rewrite !ffunE.
by case: (unlift ord0 j) => [i|] /=; rewrite ?ffunE.
Qed.

(** Source for [dgpr_time_space_hom]: the identification as an element of
    Hom(R x R^n, R^(n+1)); supporting lem:heat_extension(1). *)
Definition dgpr_time_space_hom : Hom TX W :=
  @HomMap R TX W dgpr_time_space_map (asboolT dgpr_time_space_linear).

(** Source for [dgpr_time_space_time]: coordinate 0 of the image of (s,x)
    is s; supporting lem:heat_extension(1). *)
Lemma dgpr_time_space_time (q : TX) : dgpr_time_space_map q ord0 = q.1.
Proof. by rewrite ffunE unlift_none. Qed.

(** Source for [dgpr_time_space_space]: the space part of the image of
    (s,x) is x; supporting lem:heat_extension(1). *)
Lemma dgpr_time_space_space (q : TX) : sp (dgpr_time_space_map q) = q.2.
Proof. by apply/ffunP => i; rewrite !ffunE liftK. Qed.

(** Source for [dgpr_time_space_norm]: the identification is an isometry
    for the product inner product of Federer 1.7.11; supporting
    lem:heat_extension(1). *)
Lemma dgpr_time_space_norm (q : TX) : NW (dgpr_time_space_map q) = NT q.
Proof.
apply: (inner_norm_value (@euclidean_inner_productP R n.+1)); first exact: inner_norm_nonnegative.
rewrite (inner_norm_sqr BT) product_innerE /euclidean_inner_product big_ord_recl dgpr_time_space_time.
congr (_ + _); apply: eq_bigr => i _.
by rewrite ffunE liftK.
Qed.

(** Source for [dgpr_time_space_bounded]: the identification is a bounded
    linear map (Federer 3.1.1); supporting lem:heat_extension(1). *)
Lemma dgpr_time_space_bounded : norm_bounded_linear NT NW dgpr_time_space_hom.
Proof.
exists 1; split => // q; rewrite mul1r.
by change (NW (dgpr_time_space_map q) <= NT q); rewrite dgpr_time_space_norm.
Qed.

(** Source for [dgpr_product_time_abs_le]: |s| <= |(s,x)| for the product
    inner product; supporting def:classes. *)
Lemma dgpr_product_time_abs_le (h : TX) : `|h.1| <= NT h.
Proof.
have := product_inner_first_norm_bound (scalar_inner_productP R) (@euclidean_inner_productP R n) h.
by rewrite scalar_inner_normE.
Qed.

(** Source for [dgpr_after_interior]: the half space {(s,x) : 0 < s} of
    R x R^n is open; supporting lem:heat_extension(1). *)
Lemma dgpr_after_interior (q : TX) :
  0 < q.1 -> norm_domain_interior NT (fun q' : TX => 0 < q'.1) q.
Proof.
move=> hq; exists q.1; split => // h hh /=.
have := dgpr_product_time_abs_le h; have := ler_norm (- h.1); rewrite normrN => h1 h2; lra.
Qed.

(** Source for [dgpr_before_interior]: the half space Omega_T =
    {(t,x) : t < T} of R x R^n is open (mr:notation); supporting
    lem:heat_extension(1). *)
Lemma dgpr_before_interior (T : R) (q : TX) :
  q.1 < T -> norm_domain_interior NT (fun q' : TX => q'.1 < T) q.
Proof.
move=> hq; exists (T - q.1); split; first by rewrite subr_gt0.
move=> h hh /=; have := dgpr_product_time_abs_le h; have := ler_norm h.1 => h1 h2; lra.
Qed.

(** Source for [dgpr_time_reverse_map]: the map (t,x) |-> (-t,x) of
    R x R^n; supporting the substitution s = T - t of lem:identities. *)
Definition dgpr_time_reverse_map (q : TX) : TX := (- q.1, q.2).

(** Source for [dgpr_time_reverse_linear]: the reversal is linear;
    supporting lem:heat_extension(1). *)
Lemma dgpr_time_reverse_linear : linear dgpr_time_reverse_map.
Proof.
move=> c a b; rewrite /dgpr_time_reverse_map /=.
congr (_, _); change (- (c * a.1 + b.1) = c * - a.1 + - b.1); ring.
Qed.

(** Source for [dgpr_time_reverse_hom]: the reversal as an element of
    Hom(R x R^n, R x R^n); supporting lem:heat_extension(1). *)
Definition dgpr_time_reverse_hom : Hom TX TX :=
  @HomMap R TX TX dgpr_time_reverse_map (asboolT dgpr_time_reverse_linear).

(** Source for [dgpr_time_reverse_bounded]: the reversal is an isometry,
    hence bounded; supporting lem:heat_extension(1). *)
Lemma dgpr_time_reverse_bounded : norm_bounded_linear NT NT dgpr_time_reverse_hom.
Proof.
exists 1; split => // q; rewrite mul1r.
change (NT (dgpr_time_reverse_map q) <= NT q).
suff -> : NT (dgpr_time_reverse_map q) = NT q by [].
apply: (inner_norm_value BT); first exact: inner_norm_nonnegative.
rewrite (inner_norm_sqr BT) !product_innerE /dgpr_time_reverse_map /=.
by rewrite mulrNN.
Qed.
End ProductSpace.

Section HeatSmoothProduct.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R n.+1).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation H := (@dgpr_positive_time R n).
Local Notation sp := (@dgpr_space_part R n).
Local Notation e := (@coordinate_basis R n).
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
Local Notation has_integral := (@dgpr_has_integral R X nu Z NZ hNZ).
Local Notation conv := (@dgpr_convolution R n nu hnu Z NZ hNZ hZ f).
Local Notation u := (@dgpr_heat_extension R n nu hnu Z NZ hNZ hZ f).

(** Source for [dgpr_heat_extension_smooth]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(1): the heat extension
    [(s,x) |-> u(s,x)] is of class infinity on (0,infinity) x R^n, a
    subset of R x R^n with the product inner product (Federer 1.7.11,
    3.1.11). *)
Theorem dgpr_heat_extension_smooth :
  norm_class_all_orders hNT hNZ (fun q : TX => 0 < q.1) (fun q : TX => u q.1 q.2).
Proof.
move=> k.
have h := @norm_class_precompose_linear R TX W Z NT NW NZ hNT hNW hNZ H
  (fun w => u (w ord0) (sp w)) (dgpr_time_space_hom R n) k (dgpr_time_space_bounded R n)
  (dgpr_heat_extension_class_coordinates hnu hZ hOpen hmass hsep hfmeas hfM k).
have h' := norm_class_open_restriction (B := (fun q : TX => 0 < q.1)) _ (@dgpr_after_interior R n) h.
apply: (norm_class_domain_agreement _ (h' _)).
  move=> q _; change (u (dgpr_time_space_map q ord0) (sp (dgpr_time_space_map q)) = u q.1 q.2).
  by rewrite dgpr_time_space_time dgpr_time_space_space.
move=> q hq; change (0 < dgpr_time_space_map q ord0).
by rewrite dgpr_time_space_time.
Qed.

(** Source for [dgpr_heat_extension_backward_smooth]: DPGPR 2026,
    section 3; blueprint lem:heat_extension(1) with the substitution
    s = T - t of lem:identities: [(t,x) |-> u(T - t, x)] is of class
    infinity on Omega_T = {(t,x) : t < T}. *)
Theorem dgpr_heat_extension_backward_smooth (T : R) :
  norm_class_all_orders hNT hNZ (fun q : TX => q.1 < T) (fun q : TX => u (T - q.1) q.2).
Proof.
move=> k.
have hfull (q : TX) (_ : True) : norm_domain_interior NT (fun _ => True) q := norm_full_domain_interior NT q.
have hL := norm_class_linear hNT hNT k hfull (dgpr_time_reverse_bounded R n).
have hC := norm_class_constant hNT hNT (((T : R^o), (0 : X)) : TX) k hfull.
have ha := norm_class_add hL hC.
have hc := norm_class_composition ha (dgpr_heat_extension_smooth k).
have hc' := norm_class_open_restriction (B := (fun q : TX => q.1 < T)) _ (@dgpr_before_interior R n T) hc.
apply: (norm_class_domain_agreement _ (hc' _)).
  move=> q _; change (u (- q.1 + T) (q.2 + 0) = u (T - q.1) q.2).
  by rewrite addr0 addrC.
move=> q hq; split => //; change (0 < - q.1 + T).
by rewrite addrC subr_gt0.
Qed.

(** Source for [dgpr_heat_extension_time_derivative]: DPGPR 2026,
    section 3; blueprint lem:heat_extension(1): the derivative of
    [t |-> u(t,x)] at 0 < s is the integral of
    d/ds p_s(x-y) f(y) d nu y, by differentiation under the integral sign
    (Federer 2.4.9). *)
Theorem dgpr_heat_extension_time_derivative (s : R) (x : X) : 0 < s ->
  has_normed_curve_derivative NZ (fun t => u t x) s (conv (dgpr_kernel_time_member s) x).
Proof.
move=> hs.
have hm := @dgpr_kernel_time_member_family R n.
have hs2 : 0 < s / 2 by rewrite divr_gt0.
have [C hC] := dgpr_family_uniform_bound hm (2 * s) hs2.
have hpos (t : R) : `|t| < s / 2 -> 0 < s + t *: (1 : R^o).
  by rewrite dgpr_scale_one => ht; have := ler_norm (- t); rewrite normrN => h; lra.
have hD := @dgpr_parameter_integral_directional R X nu hnu R^o Z NZ hNZ
  (fun t y => p t (x - y) *: f y) (fun t y => dgpr_kernel_time_member t (x - y) *: f y)
  (fun t => u t x) (conv (dgpr_kernel_time_member s) x) s 1 (s / 2) (fun _ => C * M) hs2.
have hD' : has_normed_curve_derivative NZ (fun r => u (s + r *: (1 : R^o)) x) 0
    (conv (dgpr_kernel_time_member s) x).
  apply: hD.
  - move=> t ht; exact: (dgpr_heat_extension_integral hnu hZ hOpen hmass hsep hfmeas hfM x (hpos t ht)).
  - exact (dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x hm hs).
  - move=> t y ht.
    have hc := dgpr_kernel_time_curve (x - y) (hpos t ht).
    rewrite dgpr_scale_one in hc.
    have hc' := dgpr_real_curve_translate hc.
    have hn := (scalar_normed_curve_derivative _ _ _).2 hc'.
    have hb : norm_bounded_linear A1 NZ (dgpr_line_hom (f y)).
      exists (NZ (f y)); split; first exact: (real_seminorm_nonnegative hNZ.1).
      by move=> h; rewrite dgpr_line_homE (real_seminorm_scale hNZ.1) mulrC.
    have hl := normed_curve_derivative_linear_image hA hb hn.
    rewrite dgpr_line_homE in hl.
    have -> : (fun r : R => p (s + r *: (1 : R^o)) (x - y) *: f y) =
      (fun r : R => dgpr_line_hom (f y) (p (s + r) (x - y))).
      by apply: funext => r; rewrite dgpr_line_homE dgpr_scale_one.
    by rewrite dgpr_scale_one.
  - exact: (dgpr_constant_summable hnu hmass (C * M)).
  - move=> t y ht.
    have hp := hpos t ht; rewrite dgpr_scale_one in hp.
    rewrite (real_seminorm_scale hNZ.1); apply: ler_pM.
    + exact: normr_ge0.
    + exact: (real_seminorm_nonnegative hNZ.1).
    + apply: hC; rewrite dgpr_scale_one; have := ler_norm t; have := ler_norm (- t); rewrite normrN => h1 h2; lra.
    + exact: hfM.
have e1 : (fun r : R => u (s + r *: (1 : R^o)) x) = (fun r => (fun t => u t x) (r + s)).
  by apply: funext => r; rewrite dgpr_scale_one addrC.
rewrite e1 in hD'.
have := (normed_curve_parameter_translation_iff NZ (fun t => u t x) s 0 _).1 hD'.
by rewrite add0r.
Qed.

(** Source for [dgpr_kernel_time_member_trace]: d/ds p_s(z) is the trace
    sum_i D^2 p_s(z)(e_i,e_i) = Delta p_s(z), lem:kernel(3) and (5). *)
Lemma dgpr_kernel_time_member_trace (s : R) (z : X) : 0 < s ->
  \sum_(i < n) @dgpr_kernel_second R n s z (e i) (e i) = dgpr_kernel_time_member s z.
Proof.
move=> hs; rewrite dgpr_kernel_time_memberE //.
rewrite (inner_norm_sqr (@euclidean_inner_productP R n) z) /euclidean_inner_product.
rewrite (eq_bigr (fun i => ((4 * s ^+ 2)^-1 * (z i * z i) - (2 * s)^-1) * p s z)); last first.
  move=> i _; rewrite dgpr_kernel_secondE !euclidean_inner_basis ffunE eqxx mulr1.
  by rewrite (mulrA ((4 * s ^+ 2)^-1)).
by rewrite -mulr_suml sumrB -mulr_sumr sumr_const card_ord mulr_natr.
Qed.

(** Source for [dgpr_heat_extension_heat]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(1), d/ds u = Delta u: the derivative of
    [t |-> u(t,x)] at 0 < s is sum_i D^2 u_s(x)(e_i,e_i), where
    D^2 u_s(x)(e_i,e_i) is the integral of D^2 p_s(x-y)(e_i,e_i) f(y)
    (dgpr_heat_extension_second). *)
Theorem dgpr_heat_extension_heat (s : R) (x : X) : 0 < s ->
  has_normed_curve_derivative NZ (fun t => u t x) s
    (\sum_(i < n) conv (fun z => @dgpr_kernel_second R n s z (e i) (e i)) x).
Proof.
move=> hs; have ht := dgpr_heat_extension_time_derivative x hs.
suff -> : \sum_(i < n) conv (fun z => @dgpr_kernel_second R n s z (e i) (e i)) x =
  conv (dgpr_kernel_time_member s) x by [].
have hI (i : 'I_n) : has_integral (fun y => @dgpr_kernel_second R n s (x - y) (e i) (e i) *: f y)
    (conv (fun z => @dgpr_kernel_second R n s z (e i) (e i)) x).
  exact: (dgpr_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x
    (dgpr_kernel_second_class_zero (e i) (e i) hs) (fun z => dgpr_kernel_second_bound z (e i) (e i) hs)).
have hS := @total_vector_integral_finite_sum R X Z NZ hNZ nu hnu (Finite.clone 'I_n _)
  (fun i y => @dgpr_kernel_second R n s (x - y) (e i) (e i) *: f y)
  (fun i => conv (fun z => @dgpr_kernel_second R n s z (e i) (e i)) x) hI.
apply/esym/(dgpr_convolution_spec hnu hZ).
have -> : (fun y => dgpr_kernel_time_member s (x - y) *: f y) =
    (fun y => \sum_(i < n) @dgpr_kernel_second R n s (x - y) (e i) (e i) *: f y).
  by apply: funext => y; rewrite -scaler_suml dgpr_kernel_time_member_trace.
exact: hS.
Qed.

(** Source for [dgpr_heat_extension_backward_heat]: DPGPR 2026, section 3;
    the substitution s = T - t of lem:identities(3): the derivative of
    [r |-> u(T - r, x)] at t < T is - Delta u_(T-t)(x). *)
Theorem dgpr_heat_extension_backward_heat (T t : R) (x : X) : t < T ->
  has_normed_curve_derivative NZ (fun r => u (T - r) x) t
    (- \sum_(i < n) conv (fun z => @dgpr_kernel_second R n (T - t) z (e i) (e i)) x).
Proof.
move=> ht; have hs : 0 < T - t by rewrite subr_gt0.
have hH := dgpr_heat_extension_heat x hs.
have hl : has_real_curve_derivative (fun r => T - r) t (-1).
  have -> : (fun r => T - r) = (fun r => T + r * (-1)) by apply: funext => r; rewrite mulrN1.
  exact: dgpr_real_curve_affine.
have := normed_curve_derivative_compose hNZ hl hH.
by rewrite scaleN1r.
Qed.
End HeatSmoothProduct.
