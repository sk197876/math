(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    lem:sv items rank and eigen: sv_m(X) > 0 exactly when
    dim im X >= m, and if 0 < a <= sv_m(X) and X* o X has an orthonormal
    basis of eigenvectors u_i with eigenvalues a_i, then at least m of
    the a_i are at least a^2 (Federer 1.7.3, 1.7.4). The dimension of the
    image is expressed by Federer's [linear_rank_at_least] (3.1.18). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerNorm InnerNormalization
  InnerProductLaws LinearBasis Hom OperatorNorm Adjoint AdjointUP AdjointCriteria
  EigenbasisUP SymmetricEigenbasis SymmetricEndomorphisms ModuleQuotient SubspaceCarrier
  GrassmannSubspaces FiniteIndependence FiniteSpans FiniteSpanSpace FiniteBasisComparison
  LinearRankAtLeast OrthonormalFamilies SimplexAffinePlaneUnivalence.
From DPGPR Require Import DgprOrthonormalCoordinates DgprSingularValueUP DgprSingularValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Rank.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m <= n)%N.

(** Source for [dgpr_unit_lower_bound]: blueprint lem:sv, proof of
    item eigen: a lower bound r >= 0 of |X(v)| on the unit vectors of
    P gives r |v| <= |X(v)| for every v in P. *)
Lemma dgpr_unit_lower_bound (X : Hom V W) (P : G V m) r :
  0 <= r -> (forall v, grassmann_val P v -> inner_norm hB v = 1 -> r <= inner_norm hC (X v)) ->
  forall v, grassmann_val P v -> r * inner_norm hB v <= inner_norm hC (X v).
Proof.
move=> hr h v hv; have [->|hv0] := eqVneq v 0.
  by rewrite inner_norm0 mulr0; exact: inner_norm_nonnegative.
have hu : grassmann_val P (inner_normalize hB v) by apply: subspace_scale.
have h1 := h _ hu (inner_normalize_norm hB hv0).
rewrite -{2}(inner_normalizeK hB hv0) linearZ_LR inner_normZ.
rewrite ger0_norm ?inner_norm_nonnegative // mulrC.
by apply: ler_wpM2l => //; exact: inner_norm_nonnegative.
Qed.

(** Source for [dgpr_sv_rank]: blueprint lem:sv item rank:
    sv_m(X) > 0 if and only if dim im X >= m. *)
Theorem dgpr_sv_rank (X : Hom V W) :
  0 < dgpr_sv hB hC he hm X <-> linear_rank_at_least X m.
Proof.
split.
- move=> hpos.
  have hr : dgpr_sv hB hC he hm X / 2 < dgpr_sv hB hC he hm X.
    by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
  have hr0 : 0 <= dgpr_sv hB hC he hm X / 2 by rewrite divr_ge0 // ltW.
  have [P hP] := dgpr_sv_approximate hr.
  have hPv := dgpr_unit_lower_bound hr0 hP.
  have [b hb] := grassmann_proof P.
  exists (fun i => subspace_val (b i)) => c hc.
  apply: (finite_basis_independent hb).
  pose v := \sum_i c i *: subspace_val (b i).
  have hv : subspace_val (\sum_i c i *: b i) = v.
    by rewrite linear_sum; apply: eq_bigr => i _; rewrite linearZ.
  have hvP : grassmann_val P v by rewrite -hv; exact: subspace_valP.
  have hXv : X v = 0.
    rewrite /v linear_sum -[RHS]hc; apply: eq_bigr => i _; exact: linearZ_LR.
  have hv0 : v = 0.
    apply/eqP; apply/negPn/negP => hv0.
    have := hPv v hvP; rewrite hXv inner_norm0.
    have hn : 0 < inner_norm hB v by rewrite inner_norm_gt0.
    have hp : 0 < dgpr_sv hB hC he hm X / 2 * inner_norm hB v.
      by rewrite mulr_gt0 // divr_gt0.
    by rewrite leNgt hp.
  by apply: subspace_val_injective; rewrite hv hv0 linear0.
- move=> [w hw].
  pose Xs := inner_adjoint hB hC he (hom_as_linear X).
  have hXs : is_adjoint B C (hom_as_linear X) Xs := inner_adjointP hB hC he (hom_as_linear X).
  have hA : is_symmetric_endomorphism B (linear_comp Xs (hom_as_linear X)).
    move=> x y; exact: (adjoint_source_square_symmetric hB hC hXs x y).
  have [u [a hu]] := symmetric_orthonormal_eigenbasis hB hA he.
  have hub := eigenbasis_basis hu; have huo := eigenbasis_orthonormal hu.
  have hue : forall i, Xs (hom_as_linear X (u i)) = a i *: u i := eigenbasis_eigenvalue hu.
  have hsq x : C (X x) (X x) = \sum_i a i * (B x (u i)) ^+ 2.
    exact: (dgpr_image_square hB hXs hub huo hue x).
  have hXu i : ~~ (0 < a i) -> X (u i) = 0.
    move=> hi; apply/eqP; rewrite -(inner_self_eq0 hC).
    rewrite -(dgpr_image_eigenvalue hB hXs huo hue i) eq_le.
    by rewrite (dgpr_image_eigenvalue_nonnegative hB hC hXs huo hue i) andbT leNgt.
  pose pr x := \sum_i (if 0 < a i then B x (u i) else 0) *: u i.
  have hpr x i : B (pr x) (u i) = if 0 < a i then B x (u i) else 0.
    exact: (dgpr_orthonormal_coefficient hB huo).
  have hXpr x : X (pr x) = X x.
    rewrite {2}(dgpr_orthonormal_expansion hB hub huo x) !linear_sum.
    apply: eq_bigr => i _; rewrite !linearZ_LR.
    case: ifP => // /negbT hi.
    by change (0 *: X (u i) = B x (u i) *: X (u i)); rewrite hXu // !scaler0.
  pose w' i := pr (w i).
  have hw' : finite_independent w'.
    move=> c hc; apply: hw.
    have hX0 := congr1 X hc; rewrite linear0 linear_sum in hX0.
    apply: (etrans _ hX0); apply: eq_bigr => i _.
    by rewrite linearZ_LR; change (c i *: X (w i) = c i *: X (pr (w i))); rewrite hXpr.
  pose P := @GrassmannSubspace R V m (finite_span_subspace w')
    (ex_intro _ (finite_span_basis w') (finite_span_basisP hw')).
  have hPv v : grassmann_val P v -> forall i, ~~ (0 < a i) -> B v (u i) = 0.
    move=> [c ->] i hi; rewrite dgpr_inner_suml //; apply: big1 => j _.
    by rewrite /w' hpr (negbTE hi) mulr0.
  pose d := \big[Order.min/1]_(i | 0 < a i) a i.
  have hd0 : 0 < d.
    by apply/bigmin_gtP; split => //; exact: ltr01.
  have hda i : 0 < a i -> d <= a i by move=> hi; exact: bigmin_le_cond.
  have hlow : Num.sqrt d <= dgpr_sv hB hC he hm X.
    apply: (dgpr_sv_lower he hm (P := P)) => v hv hv1.
    have h1 : d * B v v <= C (X v) (X v).
      rewrite hsq; apply: (dgpr_weighted_square_lower hB hub huo) => i hi.
      apply: hda; apply/negPn/negP => hai.
      by move: hi; rewrite (hPv v hv i hai) eqxx.
    have hvv : B v v = 1 by rewrite -(inner_norm_sqr hB) hv1 expr1n.
    rewrite hvv mulr1 -(inner_norm_sqr hC) in h1.
    have := ler_wsqrtr h1; rewrite sqrtr_sqr ger0_norm //.
    exact: inner_norm_nonnegative.
  by apply: lt_le_trans hlow; rewrite sqrtr_gt0.
Qed.
(** Source for [dgpr_sv_eigen]: blueprint lem:sv item eigen: if
    0 < a <= sv_m(X), u_1, ..., u_k is an orthonormal basis of V, and
    X* o X (u_i) = a_i u_i, then card { i : a_i >= a^2 } >= m. The
    proof chooses r with r^2 above every a_i < a^2 and r < a, and P in
    G(V,m) with |X(v)| >= r |v| on P; the orthogonal projection onto the
    span of { u_i : a_i >= a^2 } is injective on P. *)
Theorem dgpr_sv_eigen (X : Hom V W) (a0 : R) k (u : 'I_k -> V) (lam : 'I_k -> R) :
  0 < a0 -> a0 <= dgpr_sv hB hC he hm X -> is_basis u -> orthonormal_family B u ->
  (forall i, inner_adjoint hB hC he (hom_as_linear X) (X (u i)) = lam i *: u i) ->
  (m <= #|[set i : 'I_k | (a0 ^+ 2 <= lam i)%R]|)%N.
Proof.
move=> ha0 hsv hub huo hue.
pose Xs := inner_adjoint hB hC he (hom_as_linear X).
have hXs : is_adjoint B C (hom_as_linear X) Xs := inner_adjointP hB hC he (hom_as_linear X).
have hsq x : C (X x) (X x) = \sum_i lam i * (B x (u i)) ^+ 2.
  exact: (dgpr_image_square hB hXs hub huo hue x).
have ha2 : 0 < a0 ^+ 2 by rewrite exprn_gt0.
pose b := \big[Order.max/0]_(i | lam i < a0 ^+ 2) lam i.
have hb0 : 0 <= b.
  by have /bigmax_leP [] := lexx b.
have hbJ i : lam i < a0 ^+ 2 -> lam i <= b by move=> hi; exact: le_bigmax_cond.
have hba : b < a0 ^+ 2 by apply/bigmax_ltP; split.
have [hm1 hm2] := midf_lt hba.
have hmid0 : 0 <= (b + a0 ^+ 2) / 2 by rewrite divr_ge0 // addr_ge0 // ltW.
pose r := Num.sqrt ((b + a0 ^+ 2) / 2).
have hr0 : 0 <= r := sqrtr_ge0 _.
have hr2 : r ^+ 2 = (b + a0 ^+ 2) / 2 := sqr_sqrtr hmid0.
have hra : r < a0.
  by rewrite -[a0]ger0_norm ?ltW // -sqrtr_sqr ltr_sqrt.
have [P hP] := dgpr_sv_approximate (lt_le_trans hra hsv).
have hPv := dgpr_unit_lower_bound hr0 hP.
have hkey v : grassmann_val P v -> (forall i, a0 ^+ 2 <= lam i -> B v (u i) = 0) -> v = 0.
  move=> hv hvJ; apply/eqP; apply/negPn/negP => hv0.
  have h1 : C (X v) (X v) <= b * B v v.
    rewrite hsq; apply: (dgpr_weighted_square_upper hB hub huo) => i hi.
    apply: hbJ; rewrite ltNge; apply/negP => hle.
    by move: hi; rewrite (hvJ i hle) eqxx.
  have h2 : r ^+ 2 * B v v <= C (X v) (X v).
    rewrite -(inner_norm_sqr hB) -(inner_norm_sqr hC) -exprMn.
    apply: lerXn2r; rewrite ?nnegrE ?mulr_ge0 ?inner_norm_nonnegative //.
    exact: hPv.
  have h3 : 0 < B v v by rewrite (inner_positive hB).
  have h4 : b * B v v < r ^+ 2 * B v v by rewrite ltr_pM2r // hr2.
  by move: (le_lt_trans h1 h4); rewrite ltNge h2.
pose K := [set i : 'I_k | a0 ^+ 2 <= lam i].
pose q (j : 'I_#|K|) := u (enum_val j).
have hqo : orthonormal_family B q.
  by move=> j j'; rewrite /q huo (inj_eq enum_val_inj).
have hqi : finite_independent q := orthonormal_independent hB hqo.
pose Q := @GrassmannSubspace R V #|K| (finite_span_subspace q)
  (ex_intro _ (finite_span_basis q) (finite_span_basisP hqi)).
have [bp hbp] := grassmann_proof P.
pose pv j := subspace_val (bp j).
pose pi x := \sum_j B x (q j) *: q j.
have hpiQ x : grassmann_val Q (pi x) by exists (fun j => B x (q j)).
have hpic x j : B (pi x) (q j) = B x (q j) := dgpr_orthonormal_coefficient hB hqo _ j.
have hind : finite_independent (fun j => pi (pv j)).
  move=> c hc.
  pose v := \sum_j c j *: pv j.
  have hv : subspace_val (\sum_j c j *: bp j) = v.
    by rewrite linear_sum; apply: eq_bigr => j _; rewrite linearZ.
  have hvP : grassmann_val P v by rewrite -hv; exact: subspace_valP.
  have hvK i : a0 ^+ 2 <= lam i -> B v (u i) = 0.
    move=> hi; have hiK : i \in K by rewrite inE.
    rewrite -(enum_rankK_in hiK hiK).
    change (B v (q (enum_rank_in hiK i)) = 0).
    have h0 := congr1 (fun y => B y (q (enum_rank_in hiK i))) hc.
    have hB0 : B 0 (q (enum_rank_in hiK i)) = 0.
      by rewrite -(inner_coordinateE hB) linear0.
    rewrite /= dgpr_inner_suml // hB0 in h0.
    rewrite /v dgpr_inner_suml // -[RHS]h0; apply: eq_bigr => j _.
    by rewrite hpic.
  have hv0 := hkey v hvP hvK.
  apply: (finite_basis_independent hbp).
  by apply: subspace_val_injective; rewrite hv hv0 linear0.
exact: (independent_grassmann_bound (W := Q) (fun j => hpiQ (pv j)) hind).
Qed.
(** Source for [dgpr_sv_singular]: blueprint rem:sv_singular: if
    u_1, ..., u_n is an orthonormal basis of V, X* o X (u_i) = a_i u_i
    and a_1 >= ... >= a_n, then sv_m(X) = a_m^(1/2), the m-th singular
    value of X. Indices start at zero, so a_m is [lam i0] with
    val i0 = m - 1. *)
Theorem dgpr_sv_singular (X : Hom V W) (u : 'I_n -> V) (lam : 'I_n -> R) (i0 : 'I_n) :
  is_basis u -> orthonormal_family B u ->
  (forall i, inner_adjoint hB hC he (hom_as_linear X) (X (u i)) = lam i *: u i) ->
  (forall i j : 'I_n, (i <= j)%N -> lam j <= lam i) -> val i0 = m.-1 ->
  dgpr_sv hB hC he hm X = Num.sqrt (lam i0).
Proof.
move=> hub huo hue hdec hi0.
have /andP [hm0 hmn] := hm.
pose Xs := inner_adjoint hB hC he (hom_as_linear X).
have hXs : is_adjoint B C (hom_as_linear X) Xs := inner_adjointP hB hC he (hom_as_linear X).
have hsq x : C (X x) (X x) = \sum_i lam i * (B x (u i)) ^+ 2.
  exact: (dgpr_image_square hB hXs hub huo hue x).
have hlam0 : 0 <= lam i0 := dgpr_image_eigenvalue_nonnegative hB hC hXs huo hue i0.
pose f := fun j : 'I_m => u (widen_ord hmn j).
have hfo : orthonormal_family B f.
  move=> j j'; rewrite /f huo.
  have -> : (widen_ord hmn j == widen_ord hmn j') = (j == j').
    by apply/eqP/eqP => [h|->]; last by []; apply: val_inj; exact: (congr1 val h).
  by [].
have hfi : finite_independent f := orthonormal_independent hB hfo.
pose P := @GrassmannSubspace R V m (finite_span_subspace f)
  (ex_intro _ (finite_span_basis f) (finite_span_basisP hfi)).
have hlow : Num.sqrt (lam i0) <= dgpr_sv hB hC he hm X.
  apply: (dgpr_sv_lower he hm (P := P)) => v [c ->] hv1.
  have h1 : lam i0 * B (\sum_j c j *: f j) (\sum_j c j *: f j) <=
      C (X (\sum_j c j *: f j)) (X (\sum_j c j *: f j)).
    rewrite hsq; apply: (dgpr_weighted_square_lower hB hub huo) => i hi.
    apply: hdec; rewrite hi0 -ltnS prednK //.
    rewrite ltnNge; apply/negP => hmi; move: hi.
    rewrite dgpr_inner_suml // big1 ?eqxx // => j _.
    rewrite /f huo; case: eqP => [h|_]; last by rewrite mulr0.
    by move: (ltn_ord j); rewrite -[val j]/(val (widen_ord hmn j)) h ltnNge hmi.
  rewrite -(inner_norm_sqr hB) hv1 expr1n mulr1 -(inner_norm_sqr hC) in h1.
  have := ler_wsqrtr h1; rewrite sqrtr_sqr ger0_norm //.
  exact: inner_norm_nonnegative.
apply/eqP; rewrite eq_le hlow andbT leNgt; apply/negP => hlt.
have [ha1 ha2] := midf_lt hlt.
pose a0 := (Num.sqrt (lam i0) + dgpr_sv hB hC he hm X) / 2.
have ha0 : 0 < a0 := le_lt_trans (sqrtr_ge0 _) ha1.
have hcard := dgpr_sv_eigen ha0 (ltW ha2) hub huo hue.
have hsub : [set i : 'I_n | (a0 ^+ 2 <= lam i)%R] \subset
    [set widen_ord (ltnW (ltn_ord i0)) j | j : 'I_(val i0)].
  apply/subsetP => i; rewrite inE => hi.
  have hii : (val i < val i0)%N.
    rewrite ltnNge; apply/negP => hle.
    have hl := hdec i0 i hle.
    have : lam i0 < a0 ^+ 2.
      by rewrite -(sqr_sqrtr hlam0) ltrXn2r ?nnegrE ?sqrtr_ge0 // ltW.
    by rewrite ltNge (le_trans hi hl).
  apply/imsetP; exists (Ordinal hii) => //; exact: val_inj.
have := leq_trans hcard (leq_trans (subset_leq_card hsub) (leq_imset_card _ _)).
by rewrite card_ord hi0 leqNgt ltn_predL hm0.
Qed.
End Rank.
