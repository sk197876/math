(** Haar measures of the additive group of a finite dimensional real vector
    space, supporting Federer (1969), 2.7.16, example (2), printed pp.
    136–137: "If phi is a Haar measure of the additive group of X, then phi
    is |det|^{-m} covariant", and "(wedge^1)_# phi is a Haar measure of the
    additive group of Hom(wedge^1 V, wedge^1 V)". Here X is a vector space
    with an inner product B and a finite base, with the topology of the
    inner product (InnerMetric.v), as in HomSpaceTopology.v; its additive
    group is a locally compact Hausdorff topological group (2.7.1, p. 121).
    An orthonormal base e_1, ..., e_N of X (1.7.1, p. 28) gives the linear
    isometry Phi(x) = sum_i x_i e_i of R^N onto X with inverse Psi(y) = (y .
    e_1, ..., y . e_N). Psi carries a left Haar integral mu of X to a left
    Haar integral of R^N (2.7.2, p. 122, through the general transport of
    EquivariantPushforward.v), which is c times the Lebesgue integral of
    2.7.16, p. 134, by 2.7.7, p. 125 (finite_haar_integral_lebesgue).
    Consequently, for every linear automorphism T of X, mu(u o T) = |det
    T|^{-1} mu(u) whenever u in K(X) (finite_haar_integral_linear), with det
    of 1.3.4, p. 16: det T equals det(Psi o T o Phi) on R^N, and the latter
    is the factor of 2.7.16, p. 135, "f_#(L^n) = |det f|^{-1} L^n". For a
    Haar measure phi of X, Psi_# phi is a Haar measure of R^N, hence phi(S)
    = c L^N(Phi^{-1}(S)) for every subset S of X with some 0 < c < oo
    (finite_haar_measure_lebesgue); in particular the phi null sets are the
    Phi images of the L^N null sets. Federer uses these facts without
    comment. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology LinearBasis
  OrthonormalFamilies OrthonormalisationUP GramSchmidt InnerFiniteSynthesis EuclideanCoordinateTopology
  CoordinateProjection TensorUP ExteriorDeterminant ExteriorLeibniz EuclideanLinearMaps
  MeasureUP MeasurePushforward CompactSupportFunctionUP FunctionLatticeUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MonotoneDaniellIntegralUP ProperMapUP HomeomorphismUP
  DaniellSpacePushforward EquivariantPushforward CovariantIntegralUP HaarIntegralUP TopologicalGroupUP
  HaarIntegralUniqueness RegularPushforwardBijection TranslationInvariantHaar EuclideanLebesgueDimensions
  EuclideanAdditiveGroup EuclideanLebesgueHaar EuclideanLinearGroupCovariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Contraction.
Variable R : realType.
Variables T1 T2 : normedModType R.

(** Source for [contraction_continuous]: a map f between normed spaces
    with |f(x) - f(y)| <= |x - y| is continuous; metric background for
    the isometries of Federer 1.7.1, p. 28, used in 2.7.16, pp. 134–137.
    Supporting lemma. *)
Lemma contraction_continuous (f : T1 -> T2) :
  (forall x y, `|f x - f y| <= `|x - y|) -> continuous f.
Proof.
move=> hf x; apply/(@cvgrPdist_lt _ _ _ (nbhs x) (nbhs_filter x))=> eps heps.
apply: (filterS _ (nbhsx_ballx x _ heps))=> y; rewrite -ball_normE /= => hy.
exact: le_lt_trans (hf x y) hy.
Qed.

End Contraction.

Section OrthonormalCoordinates.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : nat.
Variable e : 'I_N -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Local Notation X := (inner_metric_space hB).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R N)).

(** Source for [orthonormal_synthesis]: Phi(x) = sum_i x_i e_i for an
    orthonormal base e of X, the linear isometry of R^N onto X of
    Federer 1.7.1, p. 28, used to identify Haar measures in 2.7.16,
    pp. 134–137. Definition. *)
Definition orthonormal_synthesis (x : R_n R N) : V := \sum_i x i *: e i.

(** Source for [orthonormal_analysis]: Psi(y) = (y . e_1, ..., y . e_N),
    the inverse of Phi, Federer 1.7.1, p. 28. Definition. *)
Definition orthonormal_analysis (y : V) : R_n R N := [ffun i => (B y (e i) : R^o)].

(** Source for [orthonormal_synthesis_linear]: Phi is linear, Federer
    1.7.1, p. 28. Supporting lemma. *)
Lemma orthonormal_synthesis_linear : linear orthonormal_synthesis.
Proof.
move=> a x y; rewrite /orthonormal_synthesis scaler_sumr -big_split /=; apply: eq_bigr=> i _.
by rewrite !ffunE scalerDl scalerA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (R_n R N) V *:%R
  orthonormal_synthesis orthonormal_synthesis_linear.

(** Source for [orthonormal_analysis_linear]: Psi is linear, Federer
    1.7.1, p. 28. Supporting lemma. *)
Lemma orthonormal_analysis_linear : linear orthonormal_analysis.
Proof.
move=> a x y; apply/ffunP=> i; rewrite /orthonormal_analysis !ffunE.
by rewrite -!(inner_coordinateE hB) linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R V (R_n R N) *:%R
  orthonormal_analysis orthonormal_analysis_linear.

(** Source for [orthonormal_synthesis_inner]: Phi(x) . e_j = x_j,
    Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma orthonormal_synthesis_inner (x : R_n R N) j : B (orthonormal_synthesis x) (e j) = x j.
Proof.
rewrite -(inner_coordinateE hB) /orthonormal_synthesis linear_sum.
rewrite (bigD1 j) // big1.
  rewrite linearZ_LR inner_coordinateE ho eqxx.
  by change (x j * 1 + 0 = x j); rewrite mulr1 addr0.
move=> i /andP[_ hi]; rewrite linearZ_LR inner_coordinateE ho (negbTE hi).
by change (x i * 0 = 0); rewrite mulr0.
Qed.

(** Source for [orthonormal_synthesisK]: Psi(Phi(x)) = x, Federer 1.7.1,
    p. 28. Supporting lemma. *)
Lemma orthonormal_synthesisK : cancel orthonormal_synthesis orthonormal_analysis.
Proof. by move=> x; apply/ffunP=> j; rewrite /orthonormal_analysis ffunE orthonormal_synthesis_inner. Qed.

(** Source for [orthonormal_analysisK]: Phi(Psi(y)) = y, Federer 1.7.1,
    p. 28 (inner_finite_synthesis_coordinates). Supporting lemma. *)
Lemma orthonormal_analysisK : cancel orthonormal_analysis orthonormal_synthesis.
Proof.
move=> y; have h := @inner_finite_synthesis_coordinates R V B hB N e he ho y.
rewrite /inner_finite_synthesis in h; rewrite -[RHS]h /orthonormal_synthesis.
by apply: eq_bigr=> i _; rewrite /orthonormal_analysis ffunE inner_coordinateE.
Qed.

(** Source for [orthonormal_synthesis_norm]: |Phi(x)| = |x|, Federer
    1.7.1, p. 28: Phi(x) . Phi(x) = sum_j x_j (Phi(x) . e_j) =
    sum_j x_j^2. Supporting lemma. *)
Lemma orthonormal_synthesis_norm (x : E) : `|(orthonormal_synthesis x : X)| = `|x|.
Proof.
rewrite !inner_norm_topologyE; apply: inner_norm_value; first exact: inner_norm_nonnegative.
rewrite inner_norm_sqr /euclidean_inner_product.
have -> : B (orthonormal_synthesis x) (orthonormal_synthesis x) =
    inner_coordinate hB (orthonormal_synthesis x) (\sum_i x i *: e i) by rewrite inner_coordinateE.
rewrite linear_sum; apply: esym; apply: eq_bigr=> i _.
rewrite linearZ_LR inner_coordinateE (inner_symmetric hB) orthonormal_synthesis_inner.
by [].
Qed.

(** Source for [orthonormal_synthesis_homeomorphism]: Phi is a
    homeomorphism of R^N onto X with inverse Psi, both being linear
    isometries, Federer 1.7.1, p. 28; supporting 2.7.16, pp. 134–137.
    Supporting lemma. *)
Lemma orthonormal_synthesis_homeomorphism :
  is_homeomorphism_with_inverse (orthonormal_synthesis : E -> X) (orthonormal_analysis : X -> E).
Proof.
have hPhi (x y : E) : `|(orthonormal_synthesis x : X) - orthonormal_synthesis y| = `|x - y|.
  by rewrite -orthonormal_synthesis_norm linearB.
split.
- by apply: contraction_continuous=> x y; rewrite hPhi.
- apply: contraction_continuous=> x y.
  rewrite -hPhi !orthonormal_analysisK.
  exact: lexx.
- exact: orthonormal_synthesisK.
- exact: orthonormal_analysisK.
Qed.

(** Source for [orthonormal_conjugate_fun]: Psi o T o Phi, the map of
    R^N corresponding to an endomorphism T of X under Phi, supporting
    Federer 2.7.16, pp. 135–137. Definition of the function. *)
Definition orthonormal_conjugate_fun (T : {linear V -> V}) (x : R_n R N) : R_n R N :=
  orthonormal_analysis (T (orthonormal_synthesis x)).

(** Source for [orthonormal_conjugate_linear]: Psi o T o Phi is linear,
    supporting Federer 2.7.16, pp. 135–137. Supporting lemma. *)
Lemma orthonormal_conjugate_linear (T : {linear V -> V}) : linear (orthonormal_conjugate_fun T).
Proof. by move=> a x y; rewrite /orthonormal_conjugate_fun !linearP. Qed.
HB.instance Definition _ (T : {linear V -> V}) := GRing.isLinear.Build R (R_n R N) (R_n R N) *:%R
  (orthonormal_conjugate_fun T) (orthonormal_conjugate_linear T).

(** Source for [orthonormal_conjugate]: Psi o T o Phi as a linear
    endomorphism of R^N, supporting Federer 2.7.16, pp. 135–137.
    Definition. *)
Definition orthonormal_conjugate (T : {linear V -> V}) : {linear R_n R N -> R_n R N} :=
  GRing.Linear.clone _ _ _ _ (orthonormal_conjugate_fun T) _.

(** Source for [orthonormal_conjugate_det]: det(Psi o T o Phi) = det T,
    Federer 1.3.4, p. 16: with a_{i,j} = T(e_i) . e_j, both maps satisfy
    the coefficient equation of the permutation formula, T(e_i) =
    sum_j a_{i,j} e_j and (Psi o T o Phi)(eps_i) = sum_j a_{i,j} eps_j.
    Supporting lemma for 2.7.16, pp. 135–137. *)
Lemma orthonormal_conjugate_det (T : {linear V -> V}) :
  euclidean_det (orthonormal_conjugate T) = det (euclidean_two_nonzero R) he T.
Proof.
pose a i j := B (T (e i)) (e j).
have hT i : T (e i) = \sum_(j < N) a i j *: e j.
  have h := @inner_finite_synthesis_coordinates R V B hB N e he ho (T (e i)).
  rewrite /inner_finite_synthesis in h; rewrite -[LHS]h.
  by apply: eq_bigr=> j _; rewrite inner_coordinateE.
have hPhi i : orthonormal_synthesis (@coordinate_basis R N i) = e i.
  rewrite /orthonormal_synthesis (bigD1 i) //= big1 ?addr0.
    by rewrite /coordinate_basis ffunE eqxx scale1r.
  by move=> j hj; rewrite /coordinate_basis ffunE (negbTE hj) scale0r.
have hC i : orthonormal_conjugate T (@coordinate_basis R N i) =
    \sum_(j < N) a i j *: @coordinate_basis R N j.
  rewrite -[LHS](@euclidean_coordinate_expansion R N); apply: eq_bigr=> j _.
  change ((orthonormal_analysis (T (orthonormal_synthesis (@coordinate_basis R N i)))) j *:
    @coordinate_basis R N j = a i j *: @coordinate_basis R N j).
  by rewrite hPhi /orthonormal_analysis ffunE.
rewrite /euclidean_det (det_formula (euclidean_two_nonzero R) (@coordinate_basisP R N) hC).
by rewrite (det_formula (euclidean_two_nonzero R) he hT).
Qed.

End OrthonormalCoordinates.

Section EuclideanHaarIntegral.
Variable R : realType.
Variable N : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R N)).
Local Notation Leb := (@euclidean_lebesgue_measure R N).

(** Source for [euclidean_lebesgue_left_haar_integral]: "L^n is the ...
    (left ...) Haar measure over R^n", Federer 2.7.16, p. 134, for the
    integral u |-> int u dL^N: it is a left Haar integral of R^N in the
    sense of 2.7.2, p. 122. Supporting lemma. *)
Lemma euclidean_lebesgue_left_haar_integral :
  is_left_haar_integral (fun x y : E => x + y) (@euclidean_lebesgue_integral R N).
Proof.
have [hC hv] := @euclidean_unit_closed_cube R N.
have hpos : (0 < Leb [set x : E | forall i, (0 <= x i <= 1)%R])%E by rewrite hv lte01.
split.
- exact: (invariant_borel_integral_left_invariant (euclidean_additive_lch_group R N)
    (@euclidean_lebesgue_invariant_borel R N)).
- exact: euclidean_lebesgue_integral_monotone.
- exact: (invariant_borel_integral_nonzero (euclidean_additive_lch_group R N)
    (@euclidean_lebesgue_invariant_borel R N) hC hpos).
Qed.

End EuclideanHaarIntegral.

Section FiniteHaar.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : nat.
Local Notation X := (inner_metric_space hB).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R N)).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KE := (@compactly_supported_continuous_functions R E).
Local Notation Leb := (@euclidean_lebesgue_measure R N).
Local Notation lebesgue := (@euclidean_lebesgue_integral R N).

Variable e : 'I_N -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Local Notation Phi := (orthonormal_synthesis e : E -> X).
Local Notation Psi := (orthonormal_analysis B e : X -> E).
(** Source for [hPhi]: Phi is a homeomorphism with inverse Psi,
    Federer 1.7.1, p. 28. *)
Let hPhi := orthonormal_synthesis_homeomorphism hB he ho.
(** Source for [hPsi]: Psi is a homeomorphism with inverse Phi,
    Federer 1.7.1, p. 28. *)
Let hPsi := homeomorphism_with_inverse_symmetric hPhi.

(** Source for [synthesis_compactly_supported]: u o Phi belongs to
    K(R^N) whenever u in K(X), Federer 2.5.19, p. 113; supporting 2.7.16,
    pp. 134–137. Supporting lemma. *)
Lemma synthesis_compactly_supported (u : X -> R) : KX u -> KE (u \o Phi).
Proof.
exact: (@compactly_supported_compose R E X Phi (homeomorphism_continuous hPhi)
  (homeomorphism_with_inverse_proper hPhi) u).
Qed.

(** Source for [analysis_left_haar_integral]: Psi carries a left Haar
    integral mu of the additive group of X to the left Haar integral
    Psi_#(mu) of R^N, Federer 2.7.2, p. 122, and 2.5.19, p. 113, since
    Psi(Phi(z) + y) = z + Psi(y). Supporting lemma. *)
Lemma analysis_left_haar_integral (mu : (X -> R) -> R) :
  is_left_haar_integral (fun f g : X => f + g) mu ->
  is_left_haar_integral (fun x y : E => x + y) (daniell_pushforward Psi mu).
Proof.
move=> hmu.
have hA : is_nonzero_monotone_invariant_integral (fun (z : E) (y : X) => Phi z + y) mu.
  case: hmu=> [[hd hl] hm hn]; split=> //; split=> // u z hu.
  exact: (hl u (Phi z) hu).
apply: (equivariant_nonzero_invariant_forward hPsi _ hA)=> z y.
rewrite /left_multiplication_action /= linearD; congr (_ + _); exact: orthonormal_synthesisK.
Qed.

(** Source for [finite_haar_integral_lebesgue]: every left Haar
    integral mu of the additive group of X satisfies
    mu(u) = c int u o Phi dL^N for u in K(X), with some c > 0, by the
    uniqueness 2.7.7, p. 125, on R^N; supporting the Haar measures of
    Federer 2.7.16, pp. 136–137. Supporting theorem. *)
Theorem finite_haar_integral_lebesgue (mu : (X -> R) -> R) :
  is_left_haar_integral (fun f g : X => f + g) mu ->
  exists2 c : R, 0 < c & forall u, KX u -> mu u = c * lebesgue (u \o Phi).
Proof.
move=> hmu.
have [c hc hcu] := left_haar_integral_unique (euclidean_additive_lch_group R N)
  (analysis_left_haar_integral hmu) (euclidean_lebesgue_left_haar_integral R N).
exists c=> // u hu.
rewrite -(hcu _ (synthesis_compactly_supported hu)) /daniell_pushforward.
congr mu; apply: funext=> y /=.
by rewrite orthonormal_analysisK.
Qed.

(** Source for [finite_haar_measure_pushforward]: if phi is a Haar
    measure of the additive group of X, then Psi_# phi is a Haar measure
    of R^N, Federer 2.7.2, p. 122, 2.5.19, p. 113, and the regularity
    of image measures under bijections (RegularPushforwardBijection.v);
    supporting "(wedge^1)_# phi is a Haar measure", 2.7.16, p. 137.
    Supporting lemma. *)
Lemma finite_haar_measure_pushforward (phi : set X -> \bar R) :
  is_left_haar_measure (fun f g : X => f + g) phi ->
  is_left_haar_measure (fun x y : E => x + y) (measure_pushforward Psi phi).
Proof.
move=> [mu [hmu hm hi hr]].
exists (daniell_pushforward Psi mu); split.
- exact: analysis_left_haar_integral.
- exact: measure_pushforward_is_measure.
- exact: (daniell_pushforward_integral (homeomorphism_continuous hPsi)
    (homeomorphism_with_inverse_proper hPsi) hm hi).
- apply: (bijection_pushforward_regular (homeomorphism_left_inverse hPsi)
    (homeomorphism_right_inverse hPsi) _ hr).
  exact: synthesis_compactly_supported.
Qed.

(** Source for [finite_haar_measure_lebesgue]: every Haar measure phi of
    the additive group of X satisfies phi(S) = c L^N(Phi^{-1}(S)) for
    every subset S of X, with some c > 0, by the uniqueness of Haar
    measures of R^N, Federer 2.7.16, p. 134 (2.7.7, p. 125); hence the
    phi null sets are the images under Phi of the L^N null sets.
    Supporting theorem for 2.7.16, p. 136. *)
Theorem finite_haar_measure_lebesgue (phi : set X -> \bar R) :
  is_left_haar_measure (fun f g : X => f + g) phi ->
  exists2 c : R, 0 < c & forall S : set X, phi S = (c%:E * Leb (Phi @^-1` S))%E.
Proof.
move=> hphi.
have [c hc hcS] := euclidean_haar_measure_multiple (or_introl (finite_haar_measure_pushforward hphi)).
exists c=> // S; rewrite -hcS /measure_pushforward.
congr phi; apply/seteqP; split=> y /=; by rewrite orthonormal_analysisK.
Qed.

End FiniteHaar.

Section FiniteHaarLinear.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : nat.
Variable b : 'I_N -> V.
Hypothesis hb : is_basis b.
Local Notation X := (inner_metric_space hB).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R N)).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KE := (@compactly_supported_continuous_functions R E).
Local Notation lebesgue := (@euclidean_lebesgue_integral R N).

(** Source for [finite_haar_integral_pullback]: for an orthonormal base
    e of X and a left Haar integral mu of the additive group of X,
    mu(v o Psi) = c int v dL^N whenever v in K(R^N), with some c > 0, by
    2.7.7, p. 125, applied to Psi_#(mu); supporting Federer 2.7.16,
    pp. 136–137. Supporting lemma. *)
Lemma finite_haar_integral_pullback (e : 'I_N -> V) (he : is_basis e)
    (ho : orthonormal_family B e) (mu : (X -> R) -> R) :
  is_left_haar_integral (fun f g : X => f + g) mu ->
  exists2 c : R, 0 < c & forall v, KE v -> mu (v \o (orthonormal_analysis B e : X -> E)) = c * lebesgue v.
Proof.
move=> hmu.
have [c hc hcu] := left_haar_integral_unique (euclidean_additive_lch_group R N)
  (analysis_left_haar_integral he ho hmu) (euclidean_lebesgue_left_haar_integral R N).
by exists c.
Qed.

(** Source for [finite_haar_integral_linear]: for a linear automorphism
    T of X and a left Haar integral mu of the additive group of X,
    mu(u o T) = |det T|^{-1} mu(u) whenever u in K(X): with an
    orthonormal base e, u o T = ((u o Phi) o (Psi o T o Phi)) o Psi,
    mu(v o Psi) = c int v dL^N, Federer 2.7.16, p. 135,
    "f_#(L^n) = |det f|^{-1} L^n", for f = Psi o T o Phi, and
    det(Psi o T o Phi) = det T (1.3.4, p. 16). This is the covariance
    factor behind "phi is |det|^{-m} covariant", 2.7.16, p. 136.
    Supporting theorem. *)
Theorem finite_haar_integral_linear (mu : (X -> R) -> R) (T : {linear V -> V}) :
  is_left_haar_integral (fun f g : X => f + g) mu ->
  det (euclidean_two_nonzero R) hb T != 0 ->
  forall u, KX u -> mu (u \o (T : X -> X)) = `|det (euclidean_two_nonzero R) hb T|^-1 * mu u.
Proof.
move=> hmu hT u hu.
have [e [he hoe]] := orthonormal_basis_exists hB hb.
have ho := orthonormalisation_orthonormal hoe.
have [c hc hcv] := finite_haar_integral_pullback he ho hmu.
pose C := orthonormal_conjugate hB e T.
have hdet : det (euclidean_two_nonzero R) hb T = euclidean_det C.
  by rewrite /C (orthonormal_conjugate_det hB he ho) (det_basis_independent _ hb he).
have hdetC : euclidean_det C != 0 by rewrite -hdet.
have [C' [hCC' hC'C]] := euclidean_linear_inverse ((euclidean_det_injective C).1 hdetC).
have hCh : is_homeomorphism_with_inverse (C : E -> E) (C' : E -> E).
  by split; [exact: euclidean_linear_continuous|exact: euclidean_linear_continuous| |].
have hPhi := orthonormal_synthesis_homeomorphism hB he ho.
have hv : KE (u \o (orthonormal_synthesis e : E -> X)).
  exact: (@compactly_supported_compose R E X _ (homeomorphism_continuous hPhi)
    (homeomorphism_with_inverse_proper hPhi) u hu).
have hvC : KE ((u \o (orthonormal_synthesis e : E -> X)) \o (C : E -> E)).
  exact: (@compactly_supported_compose R E E _ (homeomorphism_continuous hCh)
    (homeomorphism_with_inverse_proper hCh) _ hv).
have h1 : u \o (T : X -> X) =
    ((u \o (orthonormal_synthesis e : E -> X)) \o (C : E -> E)) \o (orthonormal_analysis B e : X -> E).
  apply: funext=> y /=.
  change (u (T y) = u (orthonormal_synthesis e (orthonormal_analysis B e
    (T (orthonormal_synthesis e (orthonormal_analysis B e y)))))).
  by rewrite !(orthonormal_analysisK hB he ho).
have h2 : u = (u \o (orthonormal_synthesis e : E -> X)) \o (orthonormal_analysis B e : X -> E).
  by apply: funext=> y /=; rewrite (orthonormal_analysisK hB he ho).
rewrite h1 (hcv _ hvC) (euclidean_lebesgue_linear_integral hdetC hv) [in RHS]h2 (hcv _ hv) hdet.
by rewrite mulrCA.
Qed.

End FiniteHaarLinear.

Arguments finite_haar_integral_linear {R V B} hB {N b} hb {mu T} _ _ {u} _.
Arguments finite_haar_measure_lebesgue {R V B} hB {N e} he ho {phi} _.
Arguments finite_haar_integral_lebesgue {R V B} hB {N e} he ho {mu} _.
