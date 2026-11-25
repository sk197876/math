(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Lemma 3.2; blueprint dgpr_blueprint.tex, proof of lem:DGPR32:
    supporting calculus at a fixed time. The file contains finite sums
    of integrals and the scaling of upper integrals (Federer 2.4.3(5),
    2.4.4(4)), the finite intersection of sets of full measure (Federer
    2.3.1), the representation of F in Hom(R^n, R^n) by its columns
    F(eps_j) (Federer 1.1.2, 1.7.9), the estimates (div D)^2 <= n |D|^2 and
    |trace(D o D)| <= |D|^2 (Federer 1.4.5, 1.7.9), and the comparison of
    differentials: if |f(y) - f(a)| <= K |g(y) - g(a)| for all y, then
    |Df(a)(v)| <= K |Dg(a)(v)| (Federer 3.1.1). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerNormInequalities HilbertFormCompactness FiniteCoordinates LinearBasis
  FiniteDualDimension EuclideanTraceContinuity EuclideanCoordinateMetric EuclideanStiefelInnerSplitting
  CoordinateProjection HomInner HomInnerCoordinates HomNormBound HomCompositionDeterminant
  CoefficientCoordinates OrthonormalFamilies NormDifferentialUP
  PartialFunctionUP PartialFunctionExtensionality PartialExtendedOrderLoci MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureUpperIntegralMonotone MeasureUpperIntegralScale MeasureFiniteCharacteristicIntegral
  SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprDifferentialCalculus
  DgprDivergenceIntegral DgprLemma32Spectral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Integrals.
Variable R : realType.
Variable S : choiceType.
Variable mu : set S -> \bar R.
Hypothesis hm : is_measure mu.

(** Source for [dgpr_integral_seq_sum]: Federer 2.4.4(4), p. 82: the
    integral of a finite sum of summable functions is the sum of their
    integrals. *)
Lemma dgpr_integral_seq_sum (I : Type) (s : seq I) (f : I -> S -> R) (a : I -> R) :
  (forall i, is_measure_integral mu (real_total_integrand (f i)) (a i)%:E) ->
  is_measure_integral mu (real_total_integrand (fun x => \sum_(i <- s) f i x))
    (\sum_(i <- s) a i)%:E.
Proof.
move=> hf; elim: s => [|i s ih].
  have -> : (fun x => \sum_(i <- [::]) f i x) = (fun _ => 0 : R).
    by apply: funext => x; rewrite big_nil.
  by rewrite big_nil; exact: (real_total_zero_integral hm).
have -> : (fun x => \sum_(j <- i :: s) f j x) = (fun x => f i x + \sum_(j <- s) f j x).
  by apply: funext => x; rewrite big_cons.
by rewrite big_cons; exact: (real_total_integral_add hm (hf i) ih).
Qed.

(** Source for [dgpr_integral_sum]: Federer 2.4.4(4), p. 82, for a sum
    over a finite type. *)
Lemma dgpr_integral_sum (I : finType) (f : I -> S -> R) (a : I -> R) :
  (forall i, is_measure_integral mu (real_total_integrand (f i)) (a i)%:E) ->
  is_measure_integral mu (real_total_integrand (fun x => \sum_i f i x)) (\sum_i a i)%:E.
Proof. by move=> hf; exact: (dgpr_integral_seq_sum (index_enum I) hf). Qed.

(** Source for [dgpr_upper_integral_value]: Federer 2.4.2, p. 81: the
    upper integral of a summable function is its integral. *)
Lemma dgpr_upper_integral_value (f : S -> R) (a : R) :
  is_measure_integral mu (real_total_integrand f) a%:E ->
  measure_upper_integral mu (real_total_integrand f) = a%:E.
Proof.
move=> ha.
exact: (@measure_upper_integral_unique R S mu (real_total_integrand f) _ a%:E
  (measure_upper_integral_specification mu _) ha.2.1).
Qed.

(** Source for [dgpr_upper_integral_ae_le]: Federer 2.4.3, p. 82: the
    upper integral is monotone with respect to inequality mu almost
    everywhere. *)
Lemma dgpr_upper_integral_ae_le (f g : S -> R) :
  measure_almost_everywhere mu [set x | f x <= g x] ->
  (measure_upper_integral mu (real_total_integrand f) <=
    measure_upper_integral mu (real_total_integrand g))%E.
Proof.
move=> h; apply: (measure_upper_integral_monotone hm).
apply: (measure_almost_everywhere_mono hm _ h) => x hx.
exists (f x)%:E, (g x)%:E; split; first exact/real_total_integrand_graph.
by split; [exact/real_total_integrand_graph | rewrite lee_fin].
Qed.

(** Source for [dgpr_upper_integral_scale]: Federer 2.4.3(5), p. 82:
    the upper integral of c f is c times the upper integral of f for
    0 < c < infinity. *)
Lemma dgpr_upper_integral_scale (c : R) (f : S -> R) : 0 < c ->
  measure_upper_integral mu (real_total_integrand (fun x => c * f x)) =
    (c%:E * measure_upper_integral mu (real_total_integrand f))%E.
Proof.
move=> hc; rewrite -(measure_upper_integral_positive_scale hm _ hc).
congr measure_upper_integral.
apply: partial_function_graph_extensionality => x y.
exact: iff_sym (real_total_scale_embedding_graph c f x y).
Qed.

(** Source for [dgpr_almost_everywhere_finite]: Federer 2.3.1, p. 72:
    a finite intersection of sets of full measure has full measure. *)
Lemma dgpr_almost_everywhere_finite (I : finType) (P : I -> set S) :
  (forall i, measure_almost_everywhere mu (P i)) ->
  measure_almost_everywhere mu [set x | forall i, P i x].
Proof.
move=> hP.
have hs (s : seq I) : measure_almost_everywhere mu [set x | forall i, i \in s -> P i x].
  elim: s => [|i s ih].
    apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm)) => x _ i.
    by rewrite in_nil.
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_and hm (hP i) ih)).
  move=> x [hx1 hx2] j; rewrite in_cons => /orP [/eqP -> //|hj].
  exact: hx2.
apply: (measure_almost_everywhere_mono hm _ (hs (enum I))) => x hx i.
by apply: hx; rewrite mem_enum.
Qed.
End Integrals.

Section Columns.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation eps := (@coordinate_basis R n).
Local Notation orth := (@euclidean_coordinate_orthonormal_family R n).
Local Notation BXX := (hom_inner_productP BX BX heX).
Local Notation HXX := (hom_norm BX BX heX).
Local Notation hHXX := (inner_norm_real_norm BXX).
Local Notation HI := (hom_inner BX BX heX).

(** Source for [dgpr_column]: the map [z |-> eps_j* . z] of R^n into
    Hom(R^n, R^n), with eps_j* the jth coordinate covector (Federer 1.4.5,
    p. 21, rank one maps). *)
Definition dgpr_column (j : 'I_n) : Hom X (Hom X X) :=
  hom_of_linear (coefficient_map X (dual_basis heX j)).

(** Source for [dgpr_columnE]: (eps_j* . z)(w) = w_j z. *)
Lemma dgpr_columnE j z w : dgpr_column j z w = w j *: z.
Proof.
rewrite hom_of_linearE.
change (hom_with_coefficient z (dual_basis heX j) w = w j *: z).
by rewrite hom_with_coefficientE euclidean_coordinate_dual_basis.
Qed.

(** Source for [dgpr_frame]: the endomorphism of R^n with columns
    r_1, ..., r_n, that is sum_j eps_j* . r_j (Federer 1.1.2, p. 10). *)
Definition dgpr_frame (r : 'I_n -> X) : Hom X X := \sum_j dgpr_column j (r j).

(** Source for [dgpr_frameE]: (sum_j eps_j* . r_j)(w) = sum_j w_j r_j. *)
Lemma dgpr_frameE r w : dgpr_frame r w = \sum_j w j *: r j.
Proof. by rewrite /dgpr_frame dgpr_hom_sum_apply; apply: eq_bigr => j _; rewrite dgpr_columnE. Qed.

(** Source for [dgpr_frame_eps]: the frame maps eps_i to r_i. *)
Lemma dgpr_frame_eps r i : dgpr_frame r (eps i) = r i.
Proof.
rewrite dgpr_frameE (bigD1 i) //= big1 => [|j hj].
  by rewrite /coordinate_basis ffunE eqxx scale1r addr0.
by rewrite /coordinate_basis ffunE (negbTE hj) scale0r.
Qed.

(** Source for [dgpr_frame_self]: every F in Hom(R^n, R^n) is the frame
    of its columns F(eps_j) (Federer 1.1.2, p. 10). *)
Lemma dgpr_frame_self (F : Hom X X) : dgpr_frame (fun j => F (eps j)) = F.
Proof. by apply: hom_ext => w; rewrite dgpr_frameE dgpr_coordinate_sum. Qed.

(** Source for [dgpr_frame_sqr]: |F|^2 = sum_j |F(eps_j)|^2 for the
    frame F of r (Federer 1.7.9, p. 35). *)
Lemma dgpr_frame_sqr r : HXX (dgpr_frame r) ^+ 2 = \sum_j N (r j) ^+ 2.
Proof.
rewrite (dgpr_hom_norm_sqr BX BX heX _ heX orth); apply: eq_bigr => j _.
by rewrite dgpr_frame_eps (inner_norm_sqr BX).
Qed.

(** Source for [dgpr_frame_sub]: the frame is additive in its columns. *)
Lemma dgpr_frame_sub r r' : dgpr_frame r - dgpr_frame r' = dgpr_frame (fun j => r j - r' j).
Proof.
apply: hom_ext => w; rewrite dgpr_hom_subE !dgpr_frameE -sumrB.
by apply: eq_bigr => j _; rewrite scalerBr.
Qed.

(** Source for [dgpr_column_norm]: |eps_j* . z| = |z| (Federer 1.7.9). *)
Lemma dgpr_column_norm j z : HXX (dgpr_column j z) = N z.
Proof.
have e : dgpr_column j z = dgpr_frame (fun i => if i == j then z else 0).
  apply: hom_ext => w; rewrite dgpr_columnE dgpr_frameE (bigD1 j) //= eqxx big1 => [|i hi].
    by rewrite addr0.
  by rewrite (negbTE hi) scaler0.
apply: (@pexpIrn R 2) => //; rewrite ?nnegrE ?inner_norm_nonnegative //.
rewrite e dgpr_frame_sqr (bigD1 j) //= eqxx big1 => [|i hi]; first by rewrite addr0.
by rewrite (negbTE hi) inner_norm0 expr0n.
Qed.

(** Source for [dgpr_column_bounded]: the map [z |-> eps_j* . z] is a continuous
    linear map (Federer 3.1.1). *)
Lemma dgpr_column_bounded j : norm_bounded_linear N HXX (dgpr_column j).
Proof. by exists 1; split => // z; rewrite dgpr_column_norm mul1r. Qed.

(** Source for [dgpr_frame_values]: Federer 3.1.1(3), (5), p. 210: if
    the columns [y |-> F(y)(eps_j)] are differentiable at a with
    differentials l_j, then F is differentiable at a, as a map into
    Hom(R^n, R^n) with the norm of Federer 1.7.9, and
    DF(a)(v) = sum_j eps_j* . l_j(v). *)
Lemma dgpr_frame_values (F : X -> Hom X X) (a : X) (l : 'I_n -> X -> X) :
  (forall j, dgpr_differential_values N (fun y => F y (eps j)) a (l j)) ->
  dgpr_differential_values HXX F a (fun v => dgpr_frame (fun j => l j v)).
Proof.
move=> hl.
have hc j : dgpr_differential_values HXX (fun y => dgpr_column j (F y (eps j))) a
    (fun v => dgpr_column j (l j v)).
  exact: (dgpr_values_postcompose hN hHXX (dgpr_column_bounded j) (hl j)).
have hs := dgpr_values_sum hHXX hc.
apply: (dgpr_values_ext _ _ hs) => [y|v] //.
exact: dgpr_frame_self.
Qed.

(** Source for [dgpr_divergence_inner]: div D = trace D = D . 1 with
    1 the identity of R^n, in the inner product of Federer 1.7.9; the
    identity is the frame of eps. *)
Lemma dgpr_divergence_inner (D : Hom X X) : dgpr_divergence D = HI D (dgpr_frame eps).
Proof.
rewrite dgpr_divergenceE (hom_inner_orthonormal_sum BX BX heX heX orth).
by apply: eq_bigr => i _; rewrite dgpr_frame_eps euclidean_inner_basis.
Qed.

(** Source for [dgpr_divergence_sqr]: proof of lem:DGPR32,
    (div D)^2 <= n |D|^2, by Cauchy's inequality (Federer 1.7.1) and
    |1|^2 = n (Federer 1.7.9). *)
Lemma dgpr_divergence_sqr (D : Hom X X) : dgpr_divergence D ^+ 2 <= n%:R * HXX D ^+ 2.
Proof.
have hc := inner_cauchy BXX D (dgpr_frame eps).
rewrite -dgpr_divergence_inner in hc.
have hI : HXX (dgpr_frame eps) ^+ 2 = n%:R.
  rewrite dgpr_frame_sqr (eq_bigr (fun _ => 1)) => [|i _].
    by rewrite sumr_const card_ord.
  by rewrite euclidean_coordinate_unit_norm expr1n.
have h0 : 0 <= `|dgpr_divergence D| := normr_ge0 _.
have h2 := ler_pM h0 h0 hc hc.
rewrite -(real_normK (num_real (dgpr_divergence D))) expr2.
apply: le_trans h2 _.
by rewrite mulrACA -!expr2 hI mulrC.
Qed.

(** Source for [dgpr_divergence_comp]: proof of lem:DGPR32,
    |trace(D o D)| <= |D|^2, since trace(D o D) = D . D* (Federer 1.7.4,
    1.7.9) and |D*| = |D|. *)
Lemma dgpr_divergence_comp (D : Hom X X) : `|dgpr_divergence (hom_comp D D)| <= HXX D ^+ 2.
Proof.
have e : dgpr_divergence (hom_comp D D) = HI D (dgpr_adjoint_hom BX BX heX D).
  rewrite dgpr_divergenceE (hom_inner_orthonormal_sum BX BX heX heX orth).
  apply: eq_bigr => i _.
  by rewrite hom_compE dgpr_adjoint_homP euclidean_inner_basis.
rewrite e; apply: le_trans (inner_cauchy BXX _ _) _.
change (HXX D * HXX (dgpr_adjoint_hom BX BX heX D) <= HXX D ^+ 2).
by rewrite /dgpr_adjoint_hom (dgpr_hom_norm_adjoint BX BX heX heX) -expr2.
Qed.

Section Compare.
Variables (Z1 Z2 : lmodType R) (N1 : Z1 -> R) (N2 : Z2 -> R).
Hypothesis hN1 : is_real_norm N1.
Hypothesis hN2 : is_real_norm N2.

(** Source for [dgpr_values_compare]: Federer 3.1.1, p. 209: if f and
    g are differentiable at a and |f(y) - f(a)| <= K |g(y) - g(a)| for
    every y, then |Df(a)(v)| <= K |Dg(a)(v)|; proof of lem:DGPR32,
    eq:32:DQ. *)
Lemma dgpr_values_compare (f : X -> Z1) (g : X -> Z2) (a : X) (lf : X -> Z1) (lg : X -> Z2)
    (K : R) (v : X) :
  0 <= K -> dgpr_differential_values N1 f a lf -> dgpr_differential_values N2 g a lg ->
  (forall y, N1 (f y - f a) <= K * N2 (g y - g a)) -> N1 (lf v) <= K * N2 (lg v).
Proof.
move=> hK [Lf [hLf hlf]] [Lg [hLg hlg]] hfg.
rewrite -hlf -hlg.
have hs1 := hN1.1; have hs2 := hN2.1.
have [hv0|hv] := eqVneq v 0.
  by rewrite hv0 !linear0 (real_seminorm_zero hs1) (real_seminorm_zero hs2) mulr0.
have hnv : 0 < N v by rewrite inner_norm_gt0.
apply/ler_addgt0Pr => e he.
pose eta := e / ((K + 1) * N v).
have hK1 : 0 < (K + 1) * N v by rewrite mulr_gt0 //; lra.
have heta : 0 < eta by rewrite divr_gt0.
have eeta : eta * ((K + 1) * N v) = e by rewrite /eta mulfVK // gt_eqF.
have [d1 [hd1 hr1]] := norm_differential_remainder hLf heta.
have [d2 [hd2 hr2]] := norm_differential_remainder hLg heta.
pose d := Order.min d1 d2.
have hd : 0 < d by rewrite /d lt_min hd1 hd2.
have hdd1 : d <= d1 by rewrite /d ge_min lexx.
have hdd2 : d <= d2 by rewrite /d ge_min lexx orbT.
pose tau := d / (2 * N v).
have htau : 0 < tau by rewrite divr_gt0 // mulr_gt0.
have hnt : N (tau *: v) = tau * N v by rewrite inner_normZ gtr0_norm.
have hnt2 : tau * N v = d / 2.
  by rewrite /tau; field; rewrite gt_eqF.
have hlt : N (tau *: v) < d by rewrite hnt hnt2; lra.
have r1 := hr1 (tau *: v) I (lt_le_trans hlt hdd1).
have r2 := hr2 (tau *: v) I (lt_le_trans hlt hdd2).
rewrite hnt in r1 r2.
set P1 := f (a + tau *: v) - f a in r1.
set P2 := g (a + tau *: v) - g a in r2.
have hP := hfg (a + tau *: v); rewrite -/P1 -/P2 in hP.
have e1 : Lf (tau *: v) = P1 - (P1 - Lf (tau *: v)) by rewrite opprB addrC subrK.
have t1 : N1 (Lf (tau *: v)) <= N1 P1 + N1 (P1 - Lf (tau *: v)).
  rewrite [X in N1 X <= _]e1; apply: le_trans (real_seminorm_triangle hs1 _ _) _.
  by rewrite (real_seminorm_negate hs1).
have e2 : P2 = Lg (tau *: v) + (P2 - Lg (tau *: v)) by rewrite addrC subrK.
have t2 : N2 P2 <= N2 (Lg (tau *: v)) + N2 (P2 - Lg (tau *: v)).
  by rewrite [X in N2 X <= _]e2; apply: real_seminorm_triangle.
have n1 : N1 (Lf (tau *: v)) = tau * N1 (Lf v).
  by rewrite linearZ /= (real_seminorm_scale hs1) (gtr0_norm htau).
have n2 : N2 (Lg (tau *: v)) = tau * N2 (Lg v).
  by rewrite linearZ /= (real_seminorm_scale hs2) (gtr0_norm htau).
rewrite n1 in t1; rewrite n2 in t2.
have hKt := ler_wpM2l hK (le_trans t2 (lerD (lexx _) r2)).
have hmain : tau * N1 (Lf v) <= tau * (K * N2 (Lg v) + e).
  rewrite -eeta; nra.
by rewrite -(ler_pM2l htau).
Qed.
End Compare.
End Columns.
