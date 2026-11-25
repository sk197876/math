(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3;
    blueprint dgpr_blueprint.tex, lem:regularity, first sentence and
    proof: joint bounds in (t,x) for the derivatives of the heat
    extensions with reversed time, [(t,x) |-> u(T - t, x)], and their
    Gaussian decay before T in the sense of def:classes.

    The derivatives with respect to (t,x) are Federer's higher
    differentials of 3.1.11 on R x R^n with the product inner product of
    1.7.11. They are computed on R^(n+1), with coordinate 0 as time, where
    every iterated coordinate derivative of [(s,x) |-> u(s,x)] is the
    convolution of f nu with a member of the kernel family of
    DgprHeatKernelFamily.v (differentiation under the integral sign,
    Federer 2.4.9). On a strip a <= s <= b with 0 < a, a member q of the
    kernel family satisfies |q(s,z)| <= C (1 + |z|)^K p_s(z); with
    Federer's finite coordinate bound (3.1.11, p. 223) this bounds the
    jth differential by c (1 + |x|)^K times the heat extension of |f|.
    The bound is transported to R x R^n along the affine isometry
    [(t,x) |-> (T - t, x)], using the law D^j (g o L)(p) = D^j g(L p)
    composed with L in every argument (Federer 3.1.11, chain rule), which
    is proved here for a bounded linear map L. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerNormInequalities InnerProductUP
  ScalarInnerProduct ProductInner
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureVectorIntegralUP
  SummableRealFunctionUP SummableRealArithmetic CompleteMetricUP VectorDaniellHypotheses
  MeasurableFunctionUP MeasureAlmostUP MeasureAlmostBasic TotalVectorIntegralAlmostDominatedNorm
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormDifferentialLocal NormDifferentialFiniteCalculus NormOpenDomainLaws
  NormClassOneUP NormClassZeroArithmetic NormClassZeroScalarProduct
  NormRegularity NormClassHigherUP NormedCurveDerivativeUP NormPartialDerivative
  TensorFamilyUP FamilyUpdate ConcatenatedFamilies MultilinearArguments MultilinearSuccessorArguments
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricExponentWords
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialFields
  NormHigherMultiPartialUP NormIteratedDirectionalUP NormIteratedDirectionalLaws
  MultiPartialOrderedIdentification HigherDifferentialFinitePartialBound RealCurveDerivativeUP
  ScalarNormMetricCompleteness RealExponentialUP RealExponentialSealed RealExponentialLaws
  EuclideanCoordinateMetric.
From DPGPR Require Import DgprGrowthClasses DgprParameterIntegralDifferential DgprParameterIntegralSmooth
  DgprHeatKernel DgprHeatKernelDifferential DgprHeatExtension DgprHeatKernelFamily DgprHeatExtensionSmooth
  DgprHeatExtensionBounds DgprHeatKernelHigher DgprHeatExtensionHigher DgprBackwardHeat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LinearPullback.
Variable R : realType.
Variables P X Y : lmodType R.
Variables (NP : P -> R) (NX : X -> R) (NY : Y -> R).
Hypotheses (hNP : is_real_norm NP) (hNX : is_real_norm NX) (hNY : is_real_norm NY).
Local Notation ZP := (fun k => @ContinuousMultilinear.space R k P Y NP NY hNP hNY).
Local Notation evP := (fun k => @ContinuousMultilinear.evaluation R k P Y NP NY hNP hNY).
Local Notation ZNP := (fun k => @ContinuousMultilinear.norm R k P Y NP NY hNP hNY).
Local Notation hZP := (fun k => @ContinuousMultilinear.laws R k P Y NP NY hNP hNY).
Local Notation ZX := (fun k => @ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evX := (fun k => @ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZNX := (fun k => @ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZX := (fun k => @ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable L : Hom P X.
Variable cL : R.
Hypothesis hcL : 0 <= cL.
Hypothesis hL : forall h, NX (L h) <= cL * NP h.

(** Source for [dgpr_map_arguments]: the argument family (L u_1, ...,
    L u_k) of the precomposed multilinear map; Federer 3.1.11, p. 219,
    supporting the chain rule for higher differentials. *)
Definition dgpr_map_arguments k (u : {ffun 'I_k -> P}) : {ffun 'I_k -> X} := [ffun i => L (u i)].

(** Source for [dgpr_map_arguments_with]: replacing one argument commutes
    with applying L in every argument (Federer 1.1.1, multilinearity). *)
Lemma dgpr_map_arguments_with k (u : {ffun 'I_k -> P}) (i : 'I_k) (v : P) :
  dgpr_map_arguments (family_with (i := i) u v) = family_with (i := i) (dgpr_map_arguments u) (L v).
Proof.
apply/ffunP => j; rewrite /dgpr_map_arguments ffunE.
case: (eqVneq i j) => [<-|h]; first by rewrite !family_with_in.
by rewrite !family_with_out // ffunE.
Qed.

(** Source for [dgpr_map_arguments_successor]: appending a last argument
    commutes with applying L in every argument; supporting the recursion
    of Federer 3.1.11, p. 219. *)
Lemma dgpr_map_arguments_successor k (u : {ffun 'I_k -> P}) (v : P) :
  dgpr_map_arguments (multilinear_successor_arguments u v) =
  multilinear_successor_arguments (dgpr_map_arguments u) (L v).
Proof.
apply/ffunP => i.
rewrite /dgpr_map_arguments /multilinear_successor_arguments /multilinear_arguments_cast
  /multilinear_arguments_join !ffunE /concatenate_family.
by case: (split _) => j; rewrite !ffunE.
Qed.

(** Source for [dgpr_pullback_bound]: |z(L u_1, ..., L u_k)| <=
    c^k ||z|| |u_1| ... |u_k| when |L h| <= c |h|; Federer 3.1.11,
    p. 219, the norm of a multilinear map. *)
Lemma dgpr_pullback_bound k (z : ZX k) (u : {ffun 'I_k -> P}) :
  NY (evX k (dgpr_map_arguments u) z) <= cL ^+ k * ZNX k z * \prod_(i < k) NP (u i).
Proof.
have hlaw := continuous_multilinear_norm_laws (hZX k) z.
apply: le_trans (multilinear_operator_bound hlaw (dgpr_map_arguments u)) _.
have hz := multilinear_operator_nonnegative hlaw.
have e : cL ^+ k * ZNX k z * \prod_(i < k) NP (u i) = ZNX k z * \prod_(i < k) (cL * NP (u i)).
  by rewrite big_split /= prodr_const card_ord; ring.
rewrite e; apply: ler_wpM2l => //.
apply: ler_prod => i _; rewrite /dgpr_map_arguments ffunE.
by rewrite (real_seminorm_nonnegative hNX.1) hL.
Qed.

(** Source for [dgpr_pullback_exists]: the multilinear map
    [(u_1, ..., u_k) |-> z(L u_1, ..., L u_k)] is continuous, hence an
    element of the space of Federer 3.1.11, p. 219, of norm at most
    c^k ||z||. *)
Lemma dgpr_pullback_exists k (z : ZX k) : exists w : ZP k,
  (forall u, evP k u w = evX k (dgpr_map_arguments u) z) /\ ZNP k w <= cL ^+ k * ZNX k z.
Proof.
have hz := multilinear_operator_nonnegative (continuous_multilinear_norm_laws (hZX k) z).
have hC : 0 <= cL ^+ k * ZNX k z by rewrite mulr_ge0 // exprn_ge0.
have hm : norm_bounded_multilinear NP NY (fun u => evX k (dgpr_map_arguments u) z).
  split; last by exists (cL ^+ k * ZNX k z); split => // u; exact: dgpr_pullback_bound.
  move=> x i a v w /=; rewrite !(dgpr_map_arguments_with x i) linearP.
  have hlin := continuous_multilinear_evaluation (hZX k) z; exact: (hlin (dgpr_map_arguments x) i a (L v) (L w)).
have [w hw] := continuous_multilinear_surjective (hZP k) hm.
exists w; split => //.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws (hZP k) w) hC).
by move=> u; rewrite hw; exact: dgpr_pullback_bound.
Qed.

(** Source for [dgpr_pullback_hom]: the precomposition with L in every
    argument is a bounded linear map between the spaces of continuous
    k linear maps of Federer 3.1.11, p. 219. *)
Lemma dgpr_pullback_hom k : exists Pk : Hom (ZX k) (ZP k),
  (forall z u, evP k u (Pk z) = evX k (dgpr_map_arguments u) z) /\
  (forall z, ZNP k (Pk z) <= cL ^+ k * ZNX k z).
Proof.
have [g hg] := choice (fun z => dgpr_pullback_exists (k := k) z).
have hlin : linear g.
  move=> a z1 z2; apply: (continuous_multilinear_extensional (hZP k)) => u.
  by rewrite linearP /= !(hg _).1 linearP.
exists (@HomMap R (ZX k) (ZP k) g (asboolT hlin)); split => z.
  exact: (hg z).1.
exact: (hg z).2.
Qed.

Variable b : X.
Variable A : X -> Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.
Variable f : X -> Y.

(** Source for [dgpr_pullback_interior]: the inverse image of an open set
    under the continuous affine map [p |-> L p + b] is open (Federer
    3.1.1); supporting the chain rule of 3.1.11. *)
Lemma dgpr_pullback_interior (p : P) : A (L p + b) -> norm_domain_interior NP (fun p => A (L p + b)) p.
Proof.
move=> hp; have [r [hr hb]] := hA hp.
have hc1 : 0 < cL + 1 by rewrite ltr_wpDl.
exists (r / (cL + 1)); split; first by rewrite divr_gt0.
move=> h hh.
have hNh := real_seminorm_nonnegative hNP.1 h.
have hlt : NX (L h) < r.
  apply: le_lt_trans (hL h) _.
  apply: le_lt_trans (_ : cL * NP h <= (cL + 1) * NP h) _; first by rewrite ler_wpM2r // lerDl.
  by rewrite mulrC -ltr_pdivlMr.
by have := hb _ hlt; rewrite linearD addrAC.
Qed.

(** Source for [dgpr_higher_differential_pullback]: Federer 3.1.11,
    p. 220, chain rule for the affine map [p |-> L p + b]: if D is the
    field of kth differentials of f on A, then the kth differential of
    [p |-> f(L p + b)] at p is D(L p + b) composed with L in every
    argument. *)
Theorem dgpr_higher_differential_pullback k (D : X -> ZX k) (Pk : Hom (ZX k) (ZP k)) :
  (forall z u, evP k u (Pk z) = evX k (dgpr_map_arguments u) z) ->
  (forall x, A x -> has_norm_higher_differential NX evX ZNX A f k x (D x)) ->
  forall p, A (L p + b) ->
    has_norm_higher_differential NP evP ZNP (fun p => A (L p + b)) (fun p => f (L p + b)) k p
      (Pk (D (L p + b))).
Proof.
have hLb : norm_bounded_linear NP NX L by exists cL; split.
elim: k D Pk => [|k IH] D Pk hPk hD p hp.
  have [_ h0] := hD _ hp; split => //.
  rewrite /= hPk -h0; congr (evX 0%N _ _); apply/ffunP => -[] //.
have [G hG] := norm_higher_differential_field_previous hNX hNY hZX hD.
have [Qk [hQk hQb]] := dgpr_pullback_hom k.
have hprev := IH G Qk hQk hG.
have [Lg [hLg he]] := norm_higher_differential_field_step_elim hNX hG (hD _ hp).
have hNk := continuous_multilinear_norm_is_norm hNY (hZX k).
have hT : has_norm_differential NP NX (fun _ => True) (fun p => L p + b) p (L + 0).
  exact: (norm_differential_add hNX (norm_differential_linear hNP hNX (norm_full_domain_interior NP p) hLb)
    (norm_differential_constant hNP hNX b (norm_full_domain_interior NP p))).
have hchain := norm_differential_chain hNP hNX hNk hT hLg.
have hrestrict := norm_differential_restrict (fun y (hy : A (L y + b)) => conj I hy)
  (dgpr_pullback_interior hp) hchain.
have hQkb : norm_bounded_linear (ZNX k) (ZNP k) Qk.
  by exists (cL ^+ k); split; [exact: exprn_ge0 | exact: hQb].
have hpost := norm_differential_postcompose hNP hrestrict hQkb.
apply: (norm_higher_differential_field_step hNP hNY hZP hprev hpost).
move=> u v.
have e1 : (hom_comp Qk (hom_comp Lg (L + 0))) v = Qk (Lg (L v)).
  rewrite (hom_compE Qk (hom_comp Lg (L + 0)) v) (hom_compE Lg (L + 0) v) (hom_addE L 0 v).
  by rewrite hom_zeroE addr0.
by rewrite e1 hQk he hPk dgpr_map_arguments_successor.
Qed.

End LinearPullback.

Section KernelPolynomialBound.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation p := (@dgpr_heat_kernel R n).

(** Source for [dgpr_kernel_family_polynomial_bound]: a member q of the
    kernel family, P(s^(-1),z) p_s(z) with a polynomial P, satisfies
    |q(s,z)| <= C (1 + |z|)^K p_s(z) for s >= a > 0; blueprint
    lem:kernel(4) and lem:regularity, proof. *)
Lemma dgpr_kernel_family_polynomial_bound (q : R -> X -> R) : dgpr_kernel_family q ->
  forall a : R, 0 < a -> exists C : R, exists K : nat, 0 <= C /\
    forall s z, a <= s -> `|q s z| <= C * (1 + N z) ^+ K * p s z.
Proof.
move=> hq a ha.
have hw z : 1 <= 1 + N z by rewrite lerDl; exact: inner_norm_nonnegative.
have hw0 z : 0 <= 1 + N z := le_trans ler01 (hw z).
have hp s z : a <= s -> 0 < p s z by move=> has; exact: (dgpr_kernel_gt0 z (lt_le_trans ha has)).
elim: hq => [|i q' _ [C [K [hC IH]]]|q' _ [C [K [hC IH]]]|q1 q2 _ [C1 [K1 [hC1 IH1]]] _ [C2 [K2 [hC2 IH2]]]
  |c q' _ [C [K [hC IH]]]].
- exists 1, 0%N; split => // s z has.
  by rewrite expr0 !mul1r ger0_norm // ltW // hp.
- exists C, K.+1; split => // s z has.
  have hzi : `|z i| <= 1 + N z by apply: le_trans (dgpr_coordinate_abs_le z i) _; rewrite lerDr.
  rewrite normrM; apply: le_trans (ler_pM (normr_ge0 _) (normr_ge0 _) hzi (IH s z has)) _.
  have -> : (1 + N z) * (C * (1 + N z) ^+ K * p s z) = C * (1 + N z) ^+ K.+1 * p s z by rewrite exprS; ring.
  exact: lexx.
- exists (a^-1 * C), K; split; first by rewrite mulr_ge0 // invr_ge0 ltW.
  move=> s z has; have hs : 0 < s := lt_le_trans ha has.
  have hsi : 0 < s^-1 by rewrite invr_gt0.
  rewrite normrM (gtr0_norm hsi) -!mulrA.
  apply: ler_pM; [by rewrite invr_ge0 ltW|exact: normr_ge0|by rewrite lef_pV2 ?posrE|].
  by rewrite mulrA; exact: IH.
- exists (C1 + C2), (maxn K1 K2); split; first exact: addr_ge0.
  move=> s z has; apply: le_trans (ler_normD _ _) _.
  have e1 : (1 + N z) ^+ K1 <= (1 + N z) ^+ (maxn K1 K2) := ler_weXn2l (hw z) (leq_maxl K1 K2).
  have e2 : (1 + N z) ^+ K2 <= (1 + N z) ^+ (maxn K1 K2) := ler_weXn2l (hw z) (leq_maxr K1 K2).
  have hp0 := ltW (hp s z has).
  rewrite mulrDl mulrDl; apply: lerD.
    apply: le_trans (IH1 s z has) _; rewrite ler_wpM2r // ler_wpM2l //.
  apply: le_trans (IH2 s z has) _; rewrite ler_wpM2r // ler_wpM2l //.
- exists (`|c| * C), K; split; first by rewrite mulr_ge0.
  move=> s z has; rewrite normrM -!mulrA ler_wpM2l //.
  by rewrite mulrA; exact: IH.
Qed.

End KernelPolynomialBound.

Section JointDerivatives.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R n.+1).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation H := (@dgpr_positive_time R n).
Local Notation sp := (@dgpr_space_part R n).
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
Local Notation G := (fun w : W => u (w ord0) (sp w)).
Local Notation hne := (@dgpr_heat_norm_extension R n nu hnu Z NZ f).
Local Notation ZW := (fun k => @ContinuousMultilinear.space R k W Z NW NZ hNW hNZ).
Local Notation evW := (fun k => @ContinuousMultilinear.evaluation R k W Z NW NZ hNW hNZ).
Local Notation ZNW := (fun k => @ContinuousMultilinear.norm R k W Z NW NZ hNW hNZ).
Local Notation hZW := (fun k => @ContinuousMultilinear.laws R k W Z NW NZ hNW hNZ).

(** Source for [dgpr_joint_iterated]: for every sequence j_1, ..., j_k of
    coordinates of R^(n+1), coordinate 0 being the time, there is a
    member q of the kernel family such that the iterated directional
    derivative of [(s,x) |-> u(s,x)] along e_(j_1), ..., e_(j_k) on the
    half space 0 < s (Federer 3.1.11, p. 223) at (s,x) is the convolution
    of q_s with f nu at x (differentiation under the integral sign,
    Federer 2.4.9); blueprint lem:heat_extension(1) and lem:regularity,
    proof. *)
Lemma dgpr_joint_iterated (ws : seq 'I_n.+1) : exists q, dgpr_kernel_family q /\
  forall w, H w -> has_norm_iterated_directional NZ H G [seq eW i | i <- ws] w (conv (q (w ord0)) (sp w)).
Proof.
elim: ws => [|j ws [q0 [hq0 hit]]].
  exists p; split; first exact: dgpr_kernel_family_base.
  by move=> w hw; split.
have [q1 [hq1 hd]] : exists q1, dgpr_kernel_family q1 /\ forall y w, H w ->
    has_norm_partial_derivative NZ (fun w' : W => q0 (w' ord0) (sp w' - y) *: f y) w j
      (q1 (w ord0) (sp w - y) *: f y).
  case: (unliftP ord0 j) => [i ->|->].
  - have [qi [hqi hqi']] := dgpr_kernel_family_space_derivative hq0 i.
    by exists qi; split => // y w hw; exact: (dgpr_family_partial_space hNZ f y hqi' hw).
  - have [qt [hqt hqt']] := dgpr_kernel_family_time_derivative hq0.
    by exists qt; split => // y w hw; exact: (dgpr_family_partial_time hNZ f y hqt' hw).
exists q1; split => // w hw /=.
exists (fun w' : W => conv (q0 (w' ord0)) (sp w')); split.
  move=> x z hz; have hx : H x := norm_iterated_directional_domain hz.
  exact: (norm_iterated_directional_unique hNZ (hit x hx) hz).
split.
  have [r [hr hball]] := dgpr_positive_time_interior hw.
  exists r; split => // t ht.
  have hx : H (w + t *: eW j).
    apply: hball; rewrite (real_seminorm_scale hNW.1) (@euclidean_coordinate_unit_norm R n.+1 j) mulr1.
    exact: ht.
  by exists (conv (q0 ((w + t *: eW j) ord0)) (sp (w + t *: eW j))); exact: hit.
have hI0 x : H x -> has_integral (fun y => q0 (x ord0) (sp x - y) *: f y) (conv (q0 (x ord0)) (sp x)).
  move=> hx; exact: (dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM (sp x) hq0 hx).
have hI1 := dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM (sp w) hq1 hw.
exact: (@dgpr_parameter_integral_partial R X nu hnu n.+1 Z NZ hNZ H
  (fun (x : W) (y : X) => q0 (x ord0) (sp x - y) *: f y) (fun (x : W) (y : X) => q1 (x ord0) (sp x - y) *: f y)
  (fun x : W => conv (q0 (x ord0)) (sp x)) (fun x : W => conv (q1 (x ord0)) (sp x)) w j
  hw (dgpr_positive_time_interior hw) hI0 hI1
  (fun x y hx => hd y x hx) (dgpr_family_domination hnu hNZ hmass hfM hq1 hw)).
Qed.

Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].
Hypothesis hr : 0 <= r.

(** Source for [dgpr_heat_norm_extension_ge0]: the heat extension of |f|
    is nonnegative; blueprint lem:heat_extension(2). *)
Lemma dgpr_heat_norm_extension_ge0 (s : R) (x : X) : 0 < s -> 0 <= hne s x.
Proof.
move=> hs; apply: le_trans (dgpr_heat_extension_zero_bound hnu hZ hOpen hmass hsep hfmeas hfM x hs).
exact: (real_seminorm_nonnegative hNZ.1).
Qed.

(** Source for [dgpr_family_heat_bound]: if |q(s,z)| <= C (1 + |z|)^K
    p_s(z) for s >= a > 0, then |int q_s(x-y) f(y) d nu y| <=
    C (1 + |x| + r)^K int p_s(x-y) |f(y)| d nu y, since nu is carried by
    B(0,r) (Federer 2.4.12); blueprint lem:regularity, proof. *)
Lemma dgpr_family_heat_bound (q : R -> X -> R) (a C : R) (K : nat) :
  dgpr_kernel_family q -> 0 < a -> 0 <= C ->
  (forall s z, a <= s -> `|q s z| <= C * (1 + N z) ^+ K * p s z) ->
  forall s x, a <= s -> NZ (conv (q s) x) <= C * (1 + N x + r) ^+ K * hne s x.
Proof.
move=> hq ha hC hb s x has; have hs : 0 < s := lt_le_trans ha has.
have hI := dgpr_family_convolution_integral hnu hZ hOpen hmass hsep hfmeas hfM x hq hs.
set Kc := C * (1 + N x + r) ^+ K.
have hG := real_total_integral_scale hnu Kc (dgpr_heat_norm_integral hnu hOpen hmass hfmeas hfM x hs).
apply: (total_vector_integral_almost_dominated_norm hnu hI hG).
apply: (measure_almost_everywhere_mono hnu _ hsupp) => y hy /=.
have hP := dgpr_kernel_gt0 (x - y) hs.
have hf0 := real_seminorm_nonnegative hNZ.1 (f y).
have hxy0 := inner_norm_nonnegative (@euclidean_inner_productP R n) (x - y).
rewrite (real_seminorm_scale hNZ.1).
apply: le_trans (ler_wpM2r hf0 (hb s (x - y) has)) _.
have hd : 1 + N (x - y) <= 1 + N x + r by rewrite -addrA lerD2l; exact: dgpr_distance_upper.
have h1 : 0 <= 1 + N (x - y) by rewrite addr_ge0.
have h2 : 0 <= 1 + N x + r := le_trans h1 hd.
have hpow : (1 + N (x - y)) ^+ K <= (1 + N x + r) ^+ K by apply: lerXn2r; rewrite ?nnegrE.
rewrite /Kc; have -> : C * (1 + N (x - y)) ^+ K * p s (x - y) * NZ (f y) =
  (C * (p s (x - y) * NZ (f y))) * (1 + N (x - y)) ^+ K by ring.
have -> : C * (1 + N x + r) ^+ K * (p s (x - y) * NZ (f y)) =
  (C * (p s (x - y) * NZ (f y))) * (1 + N x + r) ^+ K by ring.
by apply: ler_wpM2l => //; rewrite mulr_ge0 // mulr_ge0 // ltW.
Qed.

(** Source for [dgpr_joint_heat_bound]: for 0 < a and every k there are
    0 < c and K with ||D^k G(w)|| <= c (1 + |x| + r)^K times the
    integral of p_s(x-y) |f(y)| d nu y, for w = (s,x) in R^(n+1) with
    a <= s, where G(s,x) = u(s,x) and D^k is the kth differential of
    Federer 3.1.11 on the half space 0 < s; by
    [dgpr_joint_iterated], [dgpr_family_heat_bound] and the finite
    coordinate bound of Federer 3.1.11, p. 223; blueprint
    lem:regularity, proof. *)
Theorem dgpr_joint_heat_bound (k : nat) (a : R) : 0 < a -> exists c : R, exists K : nat, 0 < c /\
  forall (w : W) (D : ZW k), a <= w ord0 -> has_norm_higher_differential NW evW ZNW H G k w D ->
    ZNW k D <= c * (1 + N (sp w) + r) ^+ K * hne (w ord0) (sp w).
Proof.
move=> ha.
have [M0 [hM0 hMb]] := @norm_higher_differential_finite_partial_bound R n.+1 Z NZ hNZ ZW evW ZNW hZW k.
have hT : forall t : k.-tuple 'I_n.+1, exists CK : R * nat, 0 <= CK.1 /\ forall w : W, H w -> a <= w ord0 ->
    exists y : Z, has_norm_iterated_directional NZ H G [seq eW i | i <- t] w y /\
      NZ y <= CK.1 * (1 + N (sp w) + r) ^+ CK.2 * hne (w ord0) (sp w).
  move=> t; have [q [hq hu]] := dgpr_joint_iterated t.
  have [C [K [hC hb]]] := dgpr_kernel_family_polynomial_bound hq ha.
  exists (C, K); split => // w hw haw; exists (conv (q (w ord0)) (sp w)); split; first exact: hu.
  exact: (dgpr_family_heat_bound hq ha hC hb (sp w) haw).
have [Cf hCf] := choice hT.
pose Cs := \sum_(t : k.-tuple 'I_n.+1) (Cf t).1.
pose Ks := \big[maxn/0%N]_(t : k.-tuple 'I_n.+1) (Cf t).2.
have hCt t : (Cf t).1 <= Cs.
  rewrite /Cs (bigD1 t) //= lerDl; apply: sumr_ge0 => t' _; exact: (hCf t').1.
have hKt t : ((Cf t).2 <= Ks)%N by rewrite /Ks; exact: (@leq_bigmax _ (fun t0 => (Cf t0).2) t).
have hCs : 0 <= Cs by apply: sumr_ge0 => t _; exact: (hCf t).1.
exists (M0 * (Cs + 1)), Ks; split.
  by apply: mulr_gt0 => //; apply: lt_le_trans ltr01 _; rewrite lerDr.
move=> w D haw hD.
have hw : H w := lt_le_trans ha haw.
have hB : 1 <= 1 + N (sp w) + r.
  by rewrite -addrA lerDl addr_ge0 // inner_norm_nonnegative.
have hB0 : 0 <= 1 + N (sp w) + r := le_trans ler01 hB.
have hU0 := dgpr_heat_norm_extension_ge0 (sp w) hw.
set B := 1 + N (sp w) + r.
have hW0 : 0 <= B ^+ Ks * hne (w ord0) (sp w) by rewrite mulr_ge0 // exprn_ge0.
have hr0 : 0 <= Cs * (B ^+ Ks * hne (w ord0) (sp w)) by rewrite mulr_ge0.
have halpha : forall alpha : symmetric_indices n.+1 k,
    NZ (evW k (norm_multi_partial_arguments R alpha) D) <= Cs * (B ^+ Ks * hne (w ord0) (sp w)).
  move=> alpha.
  pose nus := symmetric_monomial_word idfun (symmetric_indices_unbound alpha).
  have hSize : size nus = k by rewrite /nus symmetric_monomial_word_size symmetric_indices_unbound_degree.
  have hCount i : count_mem i nus = symmetric_indices_unbound alpha i.
    have h := congr1 (fun a : symmetric_multi_index n.+1 => a i)
      (symmetric_exponent_word_count_monomial (symmetric_indices_unbound alpha)).
    by rewrite /symmetric_exponent_word_count ffunE in h.
  have hMP : has_norm_multi_partial NW evW ZNW H G alpha w (evW k (norm_multi_partial_arguments R alpha) D).
    by exists D.
  have hIt := @norm_multi_partial_to_ordered R n.+1 Z NZ hNZ ZW evW ZNW hZW H G k alpha nus w _
    hSize hCount hMP.
  have hS : size nus == k by rewrite hSize.
  have [_ hb] := hCf (Tuple hS).
  have [y [hy hyb]] := hb w hw haw.
  rewrite (norm_iterated_directional_unique hNZ hIt hy).
  apply: le_trans hyb _.
  have hpow : B ^+ (Cf (Tuple hS)).2 <= B ^+ Ks := ler_weXn2l hB (hKt _).
  rewrite -mulrA; apply: ler_pM.
  - exact: (hCf _).1.
  - by rewrite mulr_ge0 // exprn_ge0.
  - exact: hCt.
  - by apply: ler_wpM2r => //; exact: hpow.
have hDM := hMb H G w D _ hr0 hD halpha.
apply: le_trans hDM _.
have -> : M0 * (Cs + 1) * B ^+ Ks * hne (w ord0) (sp w) =
  M0 * ((Cs + 1) * (B ^+ Ks * hne (w ord0) (sp w))) by ring.
apply: ler_wpM2l; first exact: ltW.
by apply: ler_wpM2r => //; rewrite lerDl.
Qed.

End JointDerivatives.

Section GaussianTail.
Variable R : realType.
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).

(** Source for [dgpr_polynomial_gaussian_tail]: for 0 <= r, 0 < B and
    0 <= y, (1 + y)^K exp(-max(y - r, 0)^2/(4B)) <=
    ((1 + r)(2 + 8B)(K + 1))^K exp(r^2/(8B)) exp(-y^2/(16B)); this is
    the inequality max{|x| - r_0, 0}^2 >= 2^(-1) |x|^2 - r_0^2 of the
    proof of lem:regularity, combined with
    (1 + u)^K exp(-u) <= (K + 1)^K. *)
Lemma dgpr_polynomial_gaussian_tail (r B y : R) (K : nat) : 0 <= r -> 0 < B -> 0 <= y ->
  (1 + y) ^+ K * E (- (Num.max (y - r) 0) ^+ 2 / (4 * B)) <=
    ((1 + r) * (2 + 8 * B) * K.+1%:R) ^+ K * E (r ^+ 2 / (8 * B)) * E (- y ^+ 2 / (16 * B)).
Proof.
move=> hr hB hy.
set d := Num.max (y - r) 0.
have hd0 : 0 <= d by rewrite le_max lexx orbT.
have hyd : y - r <= d by rewrite le_max lexx.
have h8 : 0 < 8 * B by rewrite mulr_gt0.
set uu := d ^+ 2 / (8 * B).
have hu0 : 0 <= uu by rewrite divr_ge0 ?sqr_ge0 // ltW.
have e8 : 8 * B * uu = d ^+ 2 by rewrite /uu mulrC divfK // lt0r_neq0.
have e2 : 1 + d <= (2 + 8 * B) * (1 + uu).
  have := sqr_ge0 (d - 1); nra.
have e3 : 1 + y <= (1 + r) * (1 + d) by have := mulr_ge0 hr hd0; nra.
have hr1 : 0 <= 1 + r by rewrite addr_ge0.
have e1 : 1 + y <= (1 + r) * (2 + 8 * B) * (1 + uu).
  apply: le_trans e3 _; rewrite -mulrA; apply: ler_wpM2l => //.
have hy1 : 0 <= 1 + y by rewrite addr_ge0.
have hpow : (1 + y) ^+ K <= ((1 + r) * (2 + 8 * B)) ^+ K * (1 + uu) ^+ K.
  by rewrite -exprMn; apply: lerXn2r; rewrite ?nnegrE // ?mulr_ge0 ?addr_ge0 // ltW.
have eE : E (- d ^+ 2 / (4 * B)) = E (- uu) * E (- d ^+ 2 / (8 * B)).
  rewrite -(real_exponential_add hE); congr (E _); rewrite /uu.
  have e48 : (4 * B)^-1 = 2 * (8 * B)^-1.
    have -> : 8 * B = 2 * (4 * B) by ring.
    by rewrite [(2 * _)^-1]invfM mulrA mulfV ?mul1r // pnatr_eq0.
  rewrite !mulNr e48; ring.
have eW := dgpr_polynomial_exponential_weight K hu0.
have eT : E (- d ^+ 2 / (8 * B)) <= E (r ^+ 2 / (8 * B)) * E (- y ^+ 2 / (16 * B)).
  rewrite -(real_exponential_add hE) real_exponential_order.
  have h16 : 0 < (16 * B)^-1 by rewrite invr_gt0 mulr_gt0.
  have e816 : (8 * B)^-1 = 2 * (16 * B)^-1.
    have -> : 16 * B = 2 * (8 * B) by ring.
    by rewrite [(2 * _)^-1]invfM mulrA mulfV ?mul1r // pnatr_eq0.
  have hy2 : y ^+ 2 <= 2 * d ^+ 2 + 2 * r ^+ 2.
    have h1 : 0 <= d + r - y by lra.
    have h2 : 0 <= d + r + y by lra.
    have := mulr_ge0 h1 h2; have := sqr_ge0 (d - r); nra.
  have hpos : 0 <= 2 * d ^+ 2 + 2 * r ^+ 2 - y ^+ 2 by lra.
  have := mulr_ge0 (ltW h16) hpos.
  rewrite e816 !mulNr; nra.
have hE0 x : 0 <= E x := ltW (real_exponential_positive hE x).
have step1 : (1 + y) ^+ K * E (- uu) <= ((1 + r) * (2 + 8 * B)) ^+ K * K.+1%:R ^+ K.
  apply: le_trans (ler_wpM2r (hE0 _) hpow) _.
  rewrite -mulrA; apply: ler_wpM2l => //.
  by rewrite exprn_ge0 // mulr_ge0 // addr_ge0 // mulr_ge0 // ltW.
have -> : ((1 + r) * (2 + 8 * B) * K.+1%:R) ^+ K * E (r ^+ 2 / (8 * B)) * E (- y ^+ 2 / (16 * B)) =
  (((1 + r) * (2 + 8 * B)) ^+ K * K.+1%:R ^+ K) * (E (r ^+ 2 / (8 * B)) * E (- y ^+ 2 / (16 * B))).
  by rewrite exprMn; ring.
rewrite eE mulrA; apply: ler_pM => //.
by rewrite mulr_ge0 // exprn_ge0.
Qed.
End GaussianTail.

Section BackwardDecay.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation W := (R_n R n.+1).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R n.+1)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation BT := (product_inner_productP (scalar_inner_productP R) (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm BT).
Local Notation hNT := (inner_norm_real_norm BT).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation H := (@dgpr_positive_time R n).
Local Notation sp := (@dgpr_space_part R n).
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).
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
Variable r : R.
Hypothesis hsupp : measure_almost_everywhere nu [set y | N y <= r].
Hypothesis hr : 0 <= r.
Variable T : R.
Local Notation u := (@dgpr_heat_extension R n nu hnu Z NZ hNZ hZ f).
Local Notation hne := (@dgpr_heat_norm_extension R n nu hnu Z NZ f).
Local Notation F := (dgpr_backward_heat hnu hZ f T).
Local Notation G := (fun w : W => u (w ord0) (sp w)).
Local Notation ZT := (fun k => @ContinuousMultilinear.space R k TX Z NT NZ hNT hNZ).
Local Notation evT := (fun k => @ContinuousMultilinear.evaluation R k TX Z NT NZ hNT hNZ).
Local Notation ZNT := (fun k => @ContinuousMultilinear.norm R k TX Z NT NZ hNT hNZ).
Local Notation hZT := (fun k => @ContinuousMultilinear.laws R k TX Z NT NZ hNT hNZ).

(** Source for [dgpr_backward_linear]: the linear part of the affine
    isometry [(t,x) |-> (T - t, x)] of R x R^n onto R^(n+1), coordinate 0
    being the time; supporting lem:regularity. *)
Definition dgpr_backward_linear : Hom TX W := hom_comp (dgpr_time_space_hom R n) (dgpr_time_reverse_hom R n).

(** Source for [dgpr_backward_shift]: the translation part (T,0) of the
    same affine map; supporting lem:regularity. *)
Definition dgpr_backward_shift : W := dgpr_time_space_map ((T : R^o), (0 : X)).

Local Notation Lb := dgpr_backward_linear.
Local Notation b0 := dgpr_backward_shift.

(** Source for [dgpr_backward_affine]: the affine map sends (t,x) to
    (T - t, x); supporting lem:regularity. *)
Lemma dgpr_backward_affine (q : TX) : Lb q + b0 = dgpr_time_space_map ((T - q.1 : R^o), q.2).
Proof.
apply/ffunP => j.
change ((dgpr_time_space_map (dgpr_time_reverse_map q) + dgpr_time_space_map ((T : R^o), (0 : X))) j =
  dgpr_time_space_map ((T - q.1 : R^o), q.2) j).
rewrite !ffunE /=; case: (unlift ord0 j) => [i|] /=; first by rewrite ffunE addr0.
by rewrite addrC.
Qed.

(** Source for [dgpr_backward_time]: the time coordinate of the image of
    (t,x) is T - t; supporting lem:regularity. *)
Lemma dgpr_backward_time (q : TX) : (Lb q + b0) ord0 = T - q.1.
Proof. by rewrite dgpr_backward_affine dgpr_time_space_time. Qed.

(** Source for [dgpr_backward_space]: the space part of the image of
    (t,x) is x; supporting lem:regularity. *)
Lemma dgpr_backward_space (q : TX) : sp (Lb q + b0) = q.2.
Proof. by rewrite dgpr_backward_affine dgpr_time_space_space. Qed.

(** Source for [dgpr_backward_bounded]: the linear part is bounded
    (Federer 3.1.1); supporting lem:regularity. *)
Lemma dgpr_backward_bounded : exists cL : R, 0 <= cL /\ forall h, NW (Lb h) <= cL * NT h.
Proof. exact: (norm_bounded_linear_compose (dgpr_time_reverse_bounded R n) (dgpr_time_space_bounded R n)). Qed.

(** Source for [dgpr_backward_heat_joint_bound]: DPGPR 2026, section 3;
    blueprint lem:regularity, proof: for every j and every compact
    interval [a,b] with b < T there are 0 < c and K with
    ||D^j F(t,x)|| <= c (1 + |x|)^K int p_(T-t)(x-y) |f(y)| d nu y for
    a <= t <= b and x in R^n, where F(t,x) = u(T - t, x) and D^j is the
    jth differential with respect to (t,x) of Federer 3.1.11 on Omega_T
    (DgprGrowthClasses.v). *)
Theorem dgpr_backward_heat_joint_bound (j : nat) (a b : R) : b < T -> exists c : R, exists K : nat, 0 < c /\
  forall (q : TX) (D : ZT j), a <= q.1 <= b ->
    dgpr_higher_differential hNT hNZ (dgpr_before T) F j q D ->
    ZNT j D <= c * (1 + N q.2) ^+ K * hne (T - q.1) q.2.
Proof.
move=> hbT; have hTb : 0 < T - b by rewrite subr_gt0.
have [c1 [K [hc1 hb1]]] := dgpr_joint_heat_bound hnu hZ hOpen hmass hsep hfmeas hfM hsupp hr j hTb.
have [cL [hcL hL]] := dgpr_backward_bounded.
have [_ [DG [hDG _]]] := dgpr_heat_extension_class_coordinates hnu hZ hOpen hmass hsep hfmeas hfM j.
have [Pj [hPj hPb]] := dgpr_pullback_hom hNT hNW hNZ hcL hL j.
have hc0 : 0 <= cL ^+ j * c1 * (1 + r) ^+ K by rewrite !mulr_ge0 ?exprn_ge0 ?addr_ge0 // ltW.
exists (cL ^+ j * c1 * (1 + r) ^+ K + 1), K; split; first by rewrite ltr_wpDl.
move=> q D /andP [haq hqb] hD.
have hq : H (Lb q + b0).
  by change (0 < (Lb q + b0) ord0); rewrite dgpr_backward_time subr_gt0; exact: le_lt_trans hqb hbT.
have hpull := dgpr_higher_differential_pullback hcL hL (@dgpr_positive_time_interior R n) hPj hDG hq.
have eB : (fun q' : TX => H (Lb q' + b0)) = dgpr_before T.
  apply: funext => q'; apply: propext.
  by change (0 < (Lb q' + b0) ord0 <-> q'.1 < T); rewrite dgpr_backward_time subr_gt0.
have eF : (fun q' : TX => G (Lb q' + b0)) = F.
  apply: funext => q'.
  change (u ((Lb q' + b0) ord0) (sp (Lb q' + b0)) = u (T - q'.1) q'.2).
  by rewrite dgpr_backward_time dgpr_backward_space.
rewrite eB eF in hpull.
rewrite (norm_higher_differential_unique hNT hNZ hZT hD hpull).
apply: le_trans (hPb _) _.
have hs : T - b <= (Lb q + b0) ord0 by rewrite dgpr_backward_time lerD2l lerN2.
have hDGb := hb1 (Lb q + b0) (DG (Lb q + b0)) hs (hDG _ hq).
rewrite dgpr_backward_time dgpr_backward_space in hDGb.
have hs0 : 0 < T - q.1 by rewrite subr_gt0; exact: le_lt_trans hqb hbT.
have hU0 := dgpr_heat_norm_extension_ge0 hnu hZ hOpen hmass hsep hfmeas hfM q.2 hs0.
have hNx := inner_norm_nonnegative (@euclidean_inner_productP R n) q.2.
have hw1 : 1 + N q.2 + r <= (1 + r) * (1 + N q.2) by have := mulr_ge0 hr hNx; nra.
have hpow : (1 + N q.2 + r) ^+ K <= (1 + r) ^+ K * (1 + N q.2) ^+ K.
  by rewrite -exprMn; apply: lerXn2r; rewrite ?nnegrE ?addr_ge0 ?mulr_ge0 ?addr_ge0.
apply: le_trans (ler_wpM2l (exprn_ge0 j hcL) hDGb) _.
have -> : cL ^+ j * (c1 * (1 + N q.2 + r) ^+ K * hne (T - q.1) q.2) =
  (cL ^+ j * c1 * hne (T - q.1) q.2) * (1 + N q.2 + r) ^+ K by ring.
have -> : (cL ^+ j * c1 * (1 + r) ^+ K + 1) * (1 + N q.2) ^+ K * hne (T - q.1) q.2 =
  (cL ^+ j * c1 * hne (T - q.1) q.2) * ((1 + r) ^+ K * (1 + N q.2) ^+ K) +
  (1 + N q.2) ^+ K * hne (T - q.1) q.2 by ring.
apply: le_trans (_ : _ <= (cL ^+ j * c1 * hne (T - q.1) q.2) * ((1 + r) ^+ K * (1 + N q.2) ^+ K)) _.
  by apply: ler_wpM2l => //; rewrite !mulr_ge0 ?exprn_ge0 // ltW.
by rewrite lerDl mulr_ge0 // exprn_ge0 // addr_ge0.
Qed.

(** Source for [dgpr_backward_heat_gaussian_decay]: DPGPR 2026,
    section 3; blueprint lem:regularity, first statement for the heat
    extensions with reversed time: if nu is carried by B(0,r), then
    [(t,x) |-> u(T - t, x)] has Gaussian decay before T (def:classes).
    The proof combines [dgpr_backward_heat_joint_bound], the Gaussian
    bound lem:heat_extension(3) for the heat extension of |f|, and
    max{|x| - r, 0}^2 >= 2^(-1) |x|^2 - r^2. *)
Theorem dgpr_backward_heat_gaussian_decay : dgpr_gaussian_decay_before hNZ T F.
Proof.
split; first exact: (dgpr_heat_extension_backward_smooth hnu hZ hOpen hmass hsep hfmeas hfM T).
move=> j a b hbT.
have [c1 [K [hc1 hb1]]] := @dgpr_backward_heat_joint_bound j a b hbT.
have [bI hbI] := dgpr_norm_total_integral hnu hOpen hmass hfmeas hfM.
have hTb : 0 < T - b by rewrite subr_gt0.
set bb := Num.max (T - a) (T - b).
have hTbb : T - b <= bb by rewrite le_max lexx orbT.
have hbb : 0 < bb := lt_le_trans hTb hTbb.
set bp := Num.max bI 0.
have hbp : 0 <= bp by rewrite le_max lexx orbT.
have hE0 x : 0 <= E x := ltW (real_exponential_positive hE x).
set kc := dgpr_kernel_constant n (T - b).
have hkc : 0 <= kc := dgpr_kernel_constant_ge0 n (T - b).
set W0 := ((1 + r) * (2 + 8 * bb) * K.+1%:R) ^+ K * E (r ^+ 2 / (8 * bb)).
have hW0 : 0 <= W0 by rewrite mulr_ge0 // exprn_ge0 // !mulr_ge0 // ?addr_ge0 // ?mulr_ge0 // ltW.
set Cg := c1 * kc * bp * W0.
have hCg : 0 <= Cg by rewrite /Cg; apply: mulr_ge0 => //; apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ltW.
have h16 : 0 < 16 * bb by rewrite mulr_gt0.
exists (Cg + 16 * bb); split; first exact: ltr_wpDl.
move=> q D hqs hD; have hstrip := hqs; move/andP: hqs => [haq hqb].
have hs0 : 0 < T - q.1 by rewrite subr_gt0; exact: le_lt_trans hqb hbT.
have hbs : T - b <= T - q.1 by rewrite lerD2l lerN2.
have hsbb : T - q.1 <= bb by rewrite le_max lerD2l lerN2 haq.
set x := q.2; set y := N x.
have hy : 0 <= y := inner_norm_nonnegative (@euclidean_inner_productP R n) x.
set dlt := Num.max (y - r) 0.
have hG := dgpr_heat_extension_gauss hnu hNZ hsupp hs0
  (dgpr_heat_norm_integral hnu hOpen hmass hfmeas hfM x hs0) hbI.
have hG' : hne (T - q.1) x <= kc * E (- dlt ^+ 2 / (4 * bb)) * bp.
  apply: le_trans hG _.
  have hk := dgpr_kernel_constant_antitone n hTb hbs.
  have hk0 := dgpr_kernel_constant_ge0 n (T - q.1).
  have hex : E (- dlt ^+ 2 / (4 * (T - q.1))) <= E (- dlt ^+ 2 / (4 * bb)).
    rewrite real_exponential_order; apply: dgpr_gaussian_exponent_monotone.
      by rewrite mulr_gt0.
    by rewrite ler_wpM2l.
  apply: le_trans (_ : _ <= dgpr_kernel_constant n (T - q.1) * E (- dlt ^+ 2 / (4 * (T - q.1))) * bp) _.
    by apply: ler_wpM2l; [rewrite mulr_ge0 | rewrite le_max lexx].
  by apply: ler_wpM2r => //; apply: ler_pM.
have hJ := hb1 q D hstrip hD.
have hT := dgpr_polynomial_gaussian_tail K hr hbb hy.
rewrite /dgpr_gaussian_weight; apply: le_trans hJ _.
have hc1K : 0 <= c1 * (1 + y) ^+ K by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 // ltW.
apply: le_trans (ler_wpM2l hc1K hG') _.
have -> : c1 * (1 + y) ^+ K * (kc * E (- dlt ^+ 2 / (4 * bb)) * bp) =
  (c1 * kc * bp) * ((1 + y) ^+ K * E (- dlt ^+ 2 / (4 * bb))) by ring.
apply: le_trans (ler_wpM2l (_ : 0 <= c1 * kc * bp) hT) _.
  by rewrite !mulr_ge0 // ltW.
have -> : c1 * kc * bp * (((1 + r) * (2 + 8 * bb) * K.+1%:R) ^+ K * E (r ^+ 2 / (8 * bb)) *
  E (- y ^+ 2 / (16 * bb))) = Cg * E (- y ^+ 2 / (16 * bb)) by rewrite /Cg /W0; ring.
apply: ler_pM => //.
- by rewrite lerDl ltW.
- rewrite real_exponential_order; apply: dgpr_gaussian_exponent_monotone => //.
  by rewrite lerDr.
Qed.

End BackwardDecay.
