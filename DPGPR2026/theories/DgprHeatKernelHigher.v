(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3; blueprint
    dgpr_blueprint.tex, lem:kernel(4) for every j. The iterated coordinate
    derivatives of p_s lie in a graded family: the members of degree d are
    built from p by the operations q |-> s^(-1) z_i q (degree + 1),
    q |-> s^(-1) q (degree + 2), sums and scalar multiples; this replaces
    the polynomials P_j of the blueprint's induction. A member of degree d
    is bounded by c s^(-d/2) (1 + |z| s^(-1/2))^d p_s(z), and the partial
    derivatives of a member of degree d are members of degree d + 1. The
    jth differential of Federer 3.1.11 is then estimated through its values
    on coordinate vectors (Federer 3.1.11, p. 223). Here s^(-1/2) is
    written (sqrt s)^(-1). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerNormInequalities
  NormDifferentialUP NormClassOneUP NormRegularity NormedCurveDerivativeUP
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricExponentWords
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherMultiPartialUP
  NormIteratedDirectionalUP NormIteratedDirectionalLaws MultiPartialOrderedIdentification
  HigherDifferentialFinitePartialBound
  RealCurveDerivativeUP RealCurveDerivativeLaws RealCurveDerivativeAlgebra RealCurvePolynomialDerivatives NormPartialDerivative
  RealExponentialUP RealExponentialSealed CircularTrigonometrySealed.
From DPGPR Require Import DgprGrowthClasses DgprParameterIntegralSmooth DgprHeatKernel
  DgprHeatKernelDifferential DgprHeatExtension DgprHeatKernelFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section GradedKernelFamily.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation e := (@coordinate_basis R n).
Local Notation A1 := (fun t : R^o => `|t|).
Local Notation hA := (@scalar_absolute_value_norm R).

(** Source for [dgpr_kernel_graded]: the functions
    [(s,z) |-> s^(-d/2) P(z s^(-1/2)) p_s(z)] with a polynomial P of degree
    at most d, generated as described in the file header; they replace the
    polynomials P_j in the proof of lem:kernel(4). *)
Inductive dgpr_kernel_graded : nat -> (R -> X -> R) -> Prop :=
| dgpr_kernel_graded_base : dgpr_kernel_graded 0 p
| dgpr_kernel_graded_coordinate (d : nat) (i : 'I_n) (q : R -> X -> R) :
    dgpr_kernel_graded d q -> dgpr_kernel_graded d.+1 (fun s z => s^-1 * (z i * q s z))
| dgpr_kernel_graded_reciprocal (d : nat) (q : R -> X -> R) :
    dgpr_kernel_graded d q -> dgpr_kernel_graded d.+2 (fun s z => s^-1 * q s z)
| dgpr_kernel_graded_add (d : nat) (q1 q2 : R -> X -> R) :
    dgpr_kernel_graded d q1 -> dgpr_kernel_graded d q2 ->
    dgpr_kernel_graded d (fun s z => q1 s z + q2 s z)
| dgpr_kernel_graded_scale (d : nat) (c : R) (q : R -> X -> R) :
    dgpr_kernel_graded d q -> dgpr_kernel_graded d (fun s z => c * q s z).

(** Source for [dgpr_kernel_graded_family]: every graded member belongs to
    the kernel family of DgprHeatKernelFamily.v; lem:kernel(4). *)
Lemma dgpr_kernel_graded_family (d : nat) (q : R -> X -> R) :
  dgpr_kernel_graded d q -> dgpr_kernel_family q.
Proof.
elim => [|d' i q' _ IH|d' q' _ IH|d' q1 q2 _ IH1 _ IH2|d' c q' _ IH].
- exact (@dgpr_kernel_family_base R n).
- exact (dgpr_kernel_family_reciprocal (dgpr_kernel_family_coordinate i IH)).
- exact (dgpr_kernel_family_reciprocal IH).
- exact (dgpr_kernel_family_add IH1 IH2).
- exact (dgpr_kernel_family_scale c IH).
Qed.

(** Source for [dgpr_kernel_graded_bound]: a member of degree d is bounded
    by C s^(-d/2) (1 + |z| s^(-1/2))^d p_s(z) for 0 < s; blueprint
    lem:kernel(4), proof. *)
Lemma dgpr_kernel_graded_bound (d : nat) (q : R -> X -> R) : dgpr_kernel_graded d q ->
  exists C : R, 0 <= C /\ forall s z, 0 < s ->
    `|q s z| <= C * (Num.sqrt s)^-1 ^+ d * (1 + N z / Num.sqrt s) ^+ d * p s z.
Proof.
have hNn y : 0 <= N y := inner_norm_nonnegative (@euclidean_inner_productP R n) y.
have hsq (s : R) : 0 < s -> s^-1 = (Num.sqrt s)^-1 * (Num.sqrt s)^-1.
  by move=> hs; rewrite -invfM -expr2 sqr_sqrtr // ltW.
elim => [|d' i q' _ IH|d' q' _ IH|d' q1 q2 _ IH1 _ IH2|d' c q' _ IH].
- exists 1; split => // s z hs.
  by rewrite !expr0 !mul1r ger0_norm // ltW // dgpr_kernel_gt0.
- have [C [hC hb]] := IH; exists C; split => // s z hs.
  have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
  have hP := dgpr_kernel_gt0 z hs.
  have hsi : 0 <= s^-1 by rewrite invr_ge0 ltW.
  rewrite normrM (ger0_norm hsi) normrM.
  have h1 : `|z i| * `|q' s z| <=
      N z * (C * (Num.sqrt s)^-1 ^+ d' * (1 + N z / Num.sqrt s) ^+ d' * p s z).
    apply: ler_pM; [exact: normr_ge0 | exact: normr_ge0 | exact: dgpr_coordinate_abs_le | exact: hb].
  apply: le_trans (ler_wpM2l hsi h1) _.
  rewrite (hsq s hs); move: (Num.sqrt s) hq => w hw; move: (p s z) hP => P hP.
  set c := w^-1; have hc : 0 <= c by rewrite invr_ge0 ltW.
  have ht : 0 <= N z * c by rewrite mulr_ge0.
  have -> : c * c * (N z * (C * c ^+ d' * (1 + N z * c) ^+ d' * P)) =
    (C * c ^+ d'.+1 * P * (1 + N z * c) ^+ d') * (N z * c) by rewrite exprSr; ring.
  have -> : C * c ^+ d'.+1 * (1 + N z * c) ^+ d'.+1 * P =
    (C * c ^+ d'.+1 * P * (1 + N z * c) ^+ d') * (1 + N z * c) by rewrite [(1 + N z * c) ^+ d'.+1]exprSr; ring.
  have hK : 0 <= C * c ^+ d'.+1 * P * (1 + N z * c) ^+ d'.
    by rewrite !mulr_ge0 // ?exprn_ge0 // ?addr_ge0 // ltW.
  by apply: ler_wpM2l => //; rewrite lerDr.
- have [C [hC hb]] := IH; exists C; split => // s z hs.
  have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
  have hP := dgpr_kernel_gt0 z hs.
  have hsi : 0 <= s^-1 by rewrite invr_ge0 ltW.
  rewrite normrM (ger0_norm hsi).
  apply: le_trans (ler_wpM2l hsi (hb s z hs)) _.
  rewrite (hsq s hs); move: (Num.sqrt s) hq => w hw; move: (p s z) hP => P hP.
  set c := w^-1; have hc : 0 <= c by rewrite invr_ge0 ltW.
  have ht : 0 <= N z * c by rewrite mulr_ge0.
  move: (N z * c) ht => t ht.
  have -> : c * c * (C * c ^+ d' * (1 + t) ^+ d' * P) =
    (C * c ^+ d'.+2 * P) * (1 + t) ^+ d' by rewrite !exprSr; ring.
  have -> : C * c ^+ d'.+2 * (1 + t) ^+ d'.+2 * P = (C * c ^+ d'.+2 * P) * (1 + t) ^+ d'.+2 by ring.
  have hP0 := ltW hP.
  have hK : 0 <= C * c ^+ d'.+2 * P.
    by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: exprn_ge0.
  apply: ler_wpM2l => //.
  have h1 : 1 <= 1 + t by rewrite lerDl.
  by rewrite -(addn2 d') exprD ler_peMr // ?exprn_ge0 ?(le_trans ler01 h1) // exprn_ege1.
- have [C1 [hC1 hb1]] := IH1; have [C2 [hC2 hb2]] := IH2.
  exists (C1 + C2); split; first exact: addr_ge0.
  move=> s z hs; apply: le_trans (ler_normD _ _) _.
  by rewrite !mulrDl; apply: lerD; [exact: hb1 | exact: hb2].
- have [C [hC hb]] := IH; exists (`|c| * C); split; first by rewrite mulr_ge0.
  move=> s z hs; rewrite normrM.
  have h := ler_wpM2l (normr_ge0 c) (hb s z hs).
  move: h; move: (p s z) => P h.
  by apply: le_trans h _; rewrite !mulrA.
Qed.

(** Source for [dgpr_kernel_graded_space_derivative]: the partial
    derivatives in z of a member of degree d are members of degree d + 1;
    blueprint lem:kernel(4), proof (the recursion for P_(j+1)). *)
Lemma dgpr_kernel_graded_space_derivative (d : nat) (q : R -> X -> R) :
  dgpr_kernel_graded d q -> forall i : 'I_n, exists q', dgpr_kernel_graded d.+1 q' /\
    forall s z, 0 < s -> has_real_curve_derivative (fun t => q s (z + t *: e i)) 0 (q' s z).
Proof.
elim => [|d' j q0 hq0 IH|d' q0 hq0 IH|d' q1 q2 h1 IH1 h2 IH2|d' c q0 hq0 IH] i.
- exists (fun (s : R) (z : X) => (- 2^-1) * (s^-1 * (z i * p s z))); split.
    exact: (dgpr_kernel_graded_scale _ (dgpr_kernel_graded_coordinate i dgpr_kernel_graded_base)).
  by move=> s z hs; exact: dgpr_kernel_space_partial.
- have [qi [hqi hqi']] := IH i.
  exists (fun (s : R) (z : X) => e i j * (s^-1 * q0 s z) + s^-1 * (z j * qi s z)); split.
    exact: (dgpr_kernel_graded_add (dgpr_kernel_graded_scale (e i j) (dgpr_kernel_graded_reciprocal hq0))
      (dgpr_kernel_graded_coordinate j hqi)).
  move=> s z hs.
  have hc : has_real_curve_derivative (fun t => (z + t *: e i) j) 0 (e i j).
    have -> : (fun t => (z + t *: e i) j) = (fun t => z j + t * e i j).
      by apply: funext => t; rewrite !ffunE.
    exact: dgpr_real_curve_affine.
  have hp := real_curve_derivative_product hc (hqi' s z hs).
  move: hp; rewrite /= scale0r addr0 => hp.
  have hq := @real_curve_derivative_scale R _ _ _ s^-1 hp.
  have -> : e i j * (s^-1 * q0 s z) + s^-1 * (z j * qi s z) =
    s^-1 * (e i j * q0 s z + z j * qi s z) by ring.
  exact: hq.
- have [qi [hqi hqi']] := IH i.
  exists (fun (s : R) (z : X) => s^-1 * qi s z); split; first exact (dgpr_kernel_graded_reciprocal hqi).
  move=> s z hs; exact: (@real_curve_derivative_scale R _ _ _ s^-1 (hqi' s z hs)).
- have [r1 [hr1 hr1']] := IH1 i; have [r2 [hr2 hr2']] := IH2 i.
  exists (fun (s : R) (z : X) => r1 s z + r2 s z); split; first exact (dgpr_kernel_graded_add hr1 hr2).
  move=> s z hs; exact: dgpr_real_curve_add (hr1' s z hs) (hr2' s z hs).
- have [qi [hqi hqi']] := IH i.
  exists (fun (s : R) (z : X) => c * qi s z); split; first exact (dgpr_kernel_graded_scale c hqi).
  move=> s z hs; exact: (@real_curve_derivative_scale R _ _ _ c (hqi' s z hs)).
Qed.

(** Source for [dgpr_curve_partial]: a derivative of
    [t |-> g(a + t e_i)] at 0 is the partial derivative of g at a in the
    sense of Federer 3.1.11, p. 223; supporting lem:kernel(4). *)
Lemma dgpr_curve_partial (g : X -> R) (a : X) (i : 'I_n) (v : R) :
  has_real_curve_derivative (fun t => g (a + t *: e i)) 0 v ->
  punctured_norm_limit A1 (fun t => t^-1 *: ((g (a + t *: e i) : R^o) - g a)) v.
Proof.
move=> h; have hn := (scalar_normed_curve_derivative (fun t => g (a + t *: e i)) 0 v).2 h.
move: hn; rewrite /has_normed_curve_derivative.
have -> : (fun h0 : R => h0^-1 *: ((g (a + (0 + h0) *: e i) : R^o) - g (a + 0 *: e i))) =
  (fun t => t^-1 *: ((g (a + t *: e i) : R^o) - g a)).
  by apply: funext => t; rewrite add0r scale0r addr0.
done.
Qed.

(** Source for [dgpr_kernel_iterated]: the iterated directional
    derivative of p_s along e_(i_1), ..., e_(i_k) (Federer 3.1.11, p. 223)
    is a member of degree k; blueprint lem:kernel(4), proof. *)
Lemma dgpr_kernel_iterated (nu : seq 'I_n) : exists q, dgpr_kernel_graded (size nu) q /\
  forall s z, 0 < s ->
    has_norm_iterated_directional A1 setT (p s) [seq e i | i <- nu] z (q s z).
Proof.
elim: nu => [|i nu [q0 [hq0 hit]]].
  by exists p; split; [exact: dgpr_kernel_graded_base | move=> s z hs].
have [q1 [hq1 hd]] := dgpr_kernel_graded_space_derivative hq0 i.
exists q1; split => // s z hs /=.
exists (q0 s); split.
  move=> x w hw; exact: (norm_iterated_directional_unique hA (hit s x hs) hw).
split.
  exists 1; split; first exact: ltr01.
  by move=> t _; exists (q0 s (z + t *: e i)); exact: hit.
exact: (dgpr_curve_partial (hd s z hs)).
Qed.

(** Source for [dgpr_kernel_graded_class]: the members of the graded
    family are of class k in z for every k and 0 < s (Federer 3.1.11);
    blueprint lem:kernel(4). *)
Lemma dgpr_kernel_graded_class (k : nat) : forall (d : nat) (q : R -> X -> R),
  dgpr_kernel_graded d q -> forall s, 0 < s -> norm_class hN hA setT (q s) k.
Proof.
elim: k => [|k IH] d q hq s hs.
  apply/(@norm_class_zeroP R X R^o N A1 hN hA setT (q s)).
  exact: (dgpr_kernel_family_class_zero (dgpr_kernel_graded_family hq) hs).
have [Q hQ] := choice (dgpr_kernel_graded_space_derivative hq).
apply: (@dgpr_class_successor_coordinate_fields R n R^o A1 hA setT (q s) (fun i => Q i s) k).
- by move=> x _; exact: dgpr_interior_setT.
- exact: (dgpr_kernel_family_class_zero (dgpr_kernel_graded_family hq) hs).
- by move=> a i _; exact: (dgpr_curve_partial ((hQ i).2 s a hs)).
- by move=> i; exact: (IH _ _ (hQ i).1 s hs).
Qed.

(** Source for [dgpr_kernel_class_infinity]: p_s is of class infinity on
    R^n for 0 < s; blueprint lem:kernel(4). *)
Theorem dgpr_kernel_class_infinity (s : R) : 0 < s -> norm_class_all_orders hN hA setT (p s).
Proof. by move=> hs k; exact: (dgpr_kernel_graded_class k dgpr_kernel_graded_base hs). Qed.

(** Source for [dgpr_kernel_higher_bound]: DPGPR 2026, section 3;
    blueprint lem:kernel(4) for every j: there is 0 < c(n,j) < oo with
    ||D^j p_s(z)|| <= c(n,j) s^(-j/2) (1 + |z| s^(-1/2))^j p_s(z) for
    0 < s and z in R^n, where D^j p_s(z) is the jth differential of
    Federer 3.1.11 and ||.|| its norm (p. 219). *)
Theorem dgpr_kernel_higher_bound (k : nat) : exists c : R, 0 < c /\
  forall (s : R) (z : X) (D : @ContinuousMultilinear.space R k X R^o N A1 hN hA), 0 < s ->
    dgpr_higher_differential hN hA setT (p s) k z D ->
    @ContinuousMultilinear.norm R k X R^o N A1 hN hA D <=
      c * (Num.sqrt s)^-1 ^+ k * (1 + N z / Num.sqrt s) ^+ k * p s z.
Proof.
have [M [hM hMb]] := @norm_higher_differential_finite_partial_bound R n R^o A1 hA
  (fun j => @ContinuousMultilinear.space R j X R^o N A1 hN hA)
  (fun j => @ContinuousMultilinear.evaluation R j X R^o N A1 hN hA)
  (fun j => @ContinuousMultilinear.norm R j X R^o N A1 hN hA)
  (fun j => @ContinuousMultilinear.laws R j X R^o N A1 hN hA) k.
have hT : forall t : k.-tuple 'I_n, exists C : R, 0 <= C /\ forall s z, 0 < s -> exists y : R,
    has_norm_iterated_directional A1 setT (p s) [seq e i | i <- t] z y /\
    `|y| <= C * (Num.sqrt s)^-1 ^+ k * (1 + N z / Num.sqrt s) ^+ k * p s z.
  move=> t; have [q [hq hit]] := dgpr_kernel_iterated t.
  rewrite size_tuple in hq.
  have [C [hC hb]] := dgpr_kernel_graded_bound hq.
  by exists C; split => // s z hs; exists (q s z); split; [exact: hit | exact: hb].
have [Cf hCf] := choice hT.
pose Cs := \sum_(t : k.-tuple 'I_n) Cf t.
have hCt t : Cf t <= Cs.
  rewrite /Cs (bigD1 t) //= lerDl; apply: sumr_ge0 => t' _; exact: (hCf t').1.
have hCs : 0 <= Cs by apply: sumr_ge0 => t _; exact: (hCf t).1.
exists (M * (Cs + 1)); split.
  by apply: mulr_gt0 => //; apply: lt_le_trans ltr01 _; rewrite lerDr.
move=> s z D hs hD.
have hq : 0 < Num.sqrt s by rewrite sqrtr_gt0.
have hW : 0 <= (Num.sqrt s)^-1 ^+ k * (1 + N z / Num.sqrt s) ^+ k * p s z.
  apply: mulr_ge0; last exact: ltW (dgpr_kernel_gt0 z hs).
  have hNz := inner_norm_nonnegative (@euclidean_inner_productP R n) z.
  have hqi : 0 <= (Num.sqrt s)^-1 by rewrite invr_ge0 ltW.
  by apply: mulr_ge0; apply: exprn_ge0 => //; apply: addr_ge0 => //; exact: mulr_ge0.
have hr0 : 0 <= Cs * ((Num.sqrt s)^-1 ^+ k * (1 + N z / Num.sqrt s) ^+ k * p s z) by rewrite mulr_ge0.
have halpha : forall alpha : symmetric_indices n k,
    `|@ContinuousMultilinear.evaluation R k X R^o N A1 hN hA (norm_multi_partial_arguments R alpha) D| <=
      Cs * ((Num.sqrt s)^-1 ^+ k * (1 + N z / Num.sqrt s) ^+ k * p s z).
  move=> alpha.
  pose nu := symmetric_monomial_word idfun (symmetric_indices_unbound alpha).
  have hSize : size nu = k by rewrite /nu symmetric_monomial_word_size symmetric_indices_unbound_degree.
  have hCount i : count_mem i nu = symmetric_indices_unbound alpha i.
    have h := congr1 (fun a : symmetric_multi_index n => a i)
      (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
    by rewrite /symmetric_exponent_word_count ffunE in h.
  have hMP : has_norm_multi_partial N (fun j => @ContinuousMultilinear.evaluation R j X R^o N A1 hN hA)
      (fun j => @ContinuousMultilinear.norm R j X R^o N A1 hN hA) setT (p s) alpha z
      (@ContinuousMultilinear.evaluation R k X R^o N A1 hN hA (norm_multi_partial_arguments R alpha) D).
    by exists D.
  have hIt := @norm_multi_partial_to_ordered R n R^o A1 hA
    (fun j => @ContinuousMultilinear.space R j X R^o N A1 hN hA)
    (fun j => @ContinuousMultilinear.evaluation R j X R^o N A1 hN hA)
    (fun j => @ContinuousMultilinear.norm R j X R^o N A1 hN hA)
    (fun j => @ContinuousMultilinear.laws R j X R^o N A1 hN hA) setT (p s) k alpha nu z _ hSize hCount hMP.
  have hS : size nu == k by rewrite hSize.
  have [_ hb] := hCf (Tuple hS).
  have [y [hy hyb]] := hb s z hs.
  rewrite (norm_iterated_directional_unique hA hIt hy).
  move: hyb hW; move: (p s z) ((Num.sqrt s)^-1 ^+ k) ((1 + N z / Num.sqrt s) ^+ k) => Pz a1 a2 hyb hW.
  apply: le_trans hyb _.
  rewrite -!mulrA; apply: ler_wpM2r; [by rewrite mulrA | exact: hCt].
have hDM := hMb setT (p s) z D _ hr0 hD halpha.
move: hDM hW; move: (p s z) ((Num.sqrt s)^-1 ^+ k) ((1 + N z / Num.sqrt s) ^+ k) => Pz a1 a2 hDM hW.
apply: le_trans hDM _.
have -> : M * (Cs + 1) * a1 * a2 * Pz = M * ((Cs + 1) * (a1 * a2 * Pz)) by ring.
apply: ler_wpM2l; first exact: ltW.
by apply: ler_wpM2r => //; rewrite lerDl.
Qed.

End GradedKernelFamily.
