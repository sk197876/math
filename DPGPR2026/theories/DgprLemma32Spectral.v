(** De Philippis, Gennaioli, Pigati and Rindler (2026), proof of
    Lemma 3.2; blueprint dgpr_blueprint.tex, proof of lem:DGPR32: the
    linear algebra of the field Q = chi^(X* o X) for X in Hom(V,W). Here
    chi : R -> [0,1] is 0 on (-infinity, lambda^2/16], affine on
    [lambda^2/16, lambda^2/4] and 1 on [lambda^2/4, infinity), so that
    Lip(chi) = 16/(3 lambda^2) and chi(a)^2 <= chi(a) <= 16 a/(3 lambda^2)
    for a >= 0 (eq:32:chi). With an orthonormal basis u_i of eigenvectors
    of X* o X with eigenvalues a_i (Federer 1.7.3), Q is symmetric,
    |Q(w)|^2 = sum_i chi(a_i)^2 (u_i . w)^2 <= 16/(3 lambda^2) |X(w)|^2
    (eq:32:QB), ||Q|| <= 1, |Q|^2 = sum_i chi(a_i)^2, which is at least m
    when sv_m(X) >= lambda/2 (lem:sv, item eigen), and
    |Q(X) - Q(X')| <= Lip(chi) (|X| + |X'|) |X - X'| (lem:spectral).
    The norms are those of Federer 1.7.6 and 1.7.9. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp lra ring.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerProductLaws InnerNorm
  LinearBasis Hom HomInner HomInnerCoordinates OperatorNorm OperatorNormIdentities HomNormBound
  HomSpaceTopology Adjoint AdjointUP AdjointLaws AdjointCriteria OrthonormalFamilies InnerNormInequalities
  SymmetricEndomorphisms EigenbasisUP SymmetricEigenbasis.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprSpectralCalculusUP
  DgprSpectralCalculusSealed DgprSpectralCalculus DgprSingularValueUP DgprSingularValue
  DgprSingularValueRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Chi.
Variable R : realType.
Variable lam : R.
Hypothesis hlam : 0 < lam.

(** Source for [dgpr_clamp]: the map of R onto [0,1] that is 0 on
    (-infinity, 0], the identity on [0,1] and 1 on [1, infinity),
    supporting the definition of chi in the proof of lem:DGPR32. *)
Definition dgpr_clamp (p : R) : R := if p <= 0 then 0 else if p <= 1 then p else 1.

(** Source for [dgpr_clamp_lipschitz]: the clamp is 1-Lipschitzian
    (Federer 2.2.7). *)
Lemma dgpr_clamp_lipschitz (p q : R) : `|dgpr_clamp p - dgpr_clamp q| <= `|p - q|.
Proof.
have h1 := ler_norm (p - q).
have h2 : q - p <= `|p - q| by rewrite distrC; exact: ler_norm.
rewrite /dgpr_clamp ler_norml.
by case: (lerP p 0) => hp; case: (lerP p 1) => hp1; case: (lerP q 0) => hq;
  case: (lerP q 1) => hq1; apply/andP; split; lra.
Qed.

(** Source for [dgpr_chi]: chi of the proof of lem:DGPR32,
    chi(a) = clamp(16 a/(3 lambda^2) - 1/3). *)
Definition dgpr_chi (a : R) : R := dgpr_clamp (16 / (3 * lam ^+ 2) * a - 3^-1).

(** Source for [dgpr_chi_constant]: the number 16/(3 lambda^2) = Lip(chi); only
    the bound Lip(chi) <= 16/(3 lambda^2) is used. *)
Definition dgpr_chi_constant : R := 16 / (3 * lam ^+ 2).

(** Source for [dgpr_chi_constant_gt0]: 16/(3 lambda^2) > 0. *)
Lemma dgpr_chi_constant_gt0 : 0 < dgpr_chi_constant.
Proof. by rewrite /dgpr_chi_constant divr_gt0 // mulr_gt0 // exprn_gt0. Qed.

(** Source for [dgpr_chi_range]: 0 <= chi <= 1. *)
Lemma dgpr_chi_range (a : R) : 0 <= dgpr_chi a <= 1.
Proof.
rewrite /dgpr_chi /dgpr_clamp; set p := _ - _.
by case: (lerP p 0) => hp; case: (lerP p 1) => hp1; apply/andP; split; lra.
Qed.

(** Source for [dgpr_chi_le]: eq:32:chi, chi(a) <= 16 a/(3 lambda^2) for
    a >= 0. *)
Lemma dgpr_chi_le (a : R) : 0 <= a -> dgpr_chi a <= dgpr_chi_constant * a.
Proof.
move=> ha; have hc := dgpr_chi_constant_gt0.
have hca : 0 <= dgpr_chi_constant * a by rewrite mulr_ge0 // ltW.
rewrite /dgpr_chi -/dgpr_chi_constant /dgpr_clamp; set p := _ - _.
have hp : p = dgpr_chi_constant * a - 3^-1 by [].
have h3 : 0 < 3^-1 :> R by rewrite invr_gt0.
by case: (lerP p 0) => h0; case: (lerP p 1) => h1; lra.
Qed.

(** Source for [dgpr_chi_sqr_le]: eq:32:chi, chi(a)^2 <= chi(a). *)
Lemma dgpr_chi_sqr_le (a : R) : dgpr_chi a ^+ 2 <= dgpr_chi a.
Proof.
have /andP [h0 h1] := dgpr_chi_range a.
by rewrite expr2 -[X in _ <= X]mulr1 ler_wpM2l.
Qed.

(** Source for [dgpr_chi_one]: chi(a) = 1 for a >= lambda^2/4. *)
Lemma dgpr_chi_one (a : R) : lam ^+ 2 / 4 <= a -> dgpr_chi a = 1.
Proof.
move=> ha; rewrite /dgpr_chi /dgpr_clamp.
have hl2 : 0 < lam ^+ 2 by rewrite exprn_gt0.
have hp : 1 <= 16 / (3 * lam ^+ 2) * a - 3^-1.
  have e : 16 / (3 * lam ^+ 2) * (lam ^+ 2 / 4) = 4 / 3 :> R.
    by field; rewrite gt_eqF.
  have hc : 0 < 16 / (3 * lam ^+ 2) :> R by rewrite divr_gt0 // mulr_gt0.
  have h := ler_wpM2l (ltW hc) ha; rewrite e in h.
  have e3 : (4 / 3 : R) - 3^-1 = 1 by field.
  lra.
case: (lerP _ 0) => h0; first lra.
case: (lerP _ 1) => h1 //; lra.
Qed.

(** Source for [dgpr_chi_lipschitz]: |chi(a) - chi(b)| <=
    16/(3 lambda^2) |a - b| (Federer 2.2.7). *)
Lemma dgpr_chi_lipschitz (a b : R) : `|dgpr_chi a - dgpr_chi b| <= dgpr_chi_constant * `|a - b|.
Proof.
apply: le_trans (dgpr_clamp_lipschitz _ _) _.
have e : 16 / (3 * lam ^+ 2) * a - 3^-1 - (16 / (3 * lam ^+ 2) * b - 3^-1) =
  dgpr_chi_constant * (a - b) by rewrite /dgpr_chi_constant; ring.
by rewrite e normrM ger0_norm // ltW // dgpr_chi_constant_gt0.
Qed.
End Chi.

Section InnerSub.
Variable R : realType.
Variable Z : lmodType R.
Variable D : Z -> Z -> R.
Hypothesis hD : is_inner_product D.

(** Source for [dgpr_inner_subr]: Federer 1.7.1, p. 28, linearity of the
    inner product in its second argument. *)
Lemma dgpr_inner_subr x a b : D x (a - b) = D x a - D x b.
Proof.
rewrite (inner_symmetric hD) -(inner_coordinateE hD) linearB !(inner_coordinateE hD).
by rewrite !(inner_symmetric hD x).
Qed.

(** Source for [dgpr_inner_subl]: Federer 1.7.1, p. 28, linearity of the
    inner product in its first argument. *)
Lemma dgpr_inner_subl x a b : D (a - b) x = D a x - D b x.
Proof. by rewrite !(inner_symmetric hD _ x) dgpr_inner_subr. Qed.

(** Source for [dgpr_hom_subE]: Federer 1.4.1, p. 17, the operations of
    Hom(Z, U) are pointwise. *)
Lemma dgpr_hom_subE (U : lmodType R) (F G : Hom Z U) x : (F - G) x = F x - G x.
Proof. by []. Qed.
End InnerSub.

Section Spectral.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable d : nat.
Variable f : 'I_d -> W.
Hypothesis hf : is_basis f.
Variable m : nat.
Hypothesis hm : (0 < m <= n)%N.
Variable lam : R.
Hypothesis hlam : 0 < lam.
Local Notation NV := (inner_norm hB).
Local Notation NW := (inner_norm hC).
Local Notation HV := (hom_norm hB hB he).
Local Notation HX := (hom_norm hB hC he).
Local Notation chi := (dgpr_chi lam).
Local Notation c := (dgpr_chi_constant lam).

(** Source for [dgpr_adjoint_hom]: X* in Hom(W,V), Federer 1.7.4. *)
Definition dgpr_adjoint_hom (X : Hom V W) : Hom W V :=
  hom_of_linear (inner_adjoint hB hC he (hom_as_linear X)).

(** Source for [dgpr_adjoint_homP]: B(x, X*(y)) = C(X(x), y), Federer
    1.7.4. *)
Lemma dgpr_adjoint_homP (X : Hom V W) x y : B x (dgpr_adjoint_hom X y) = C (X x) y.
Proof.
by rewrite /dgpr_adjoint_hom hom_of_linearE (inner_adjointP hB hC he (hom_as_linear X)) hom_as_linearE.
Qed.

(** Source for [dgpr_adjoint_hom_sub]: (X - X')* = X* - X'*, by the
    uniqueness of adjoints (Federer 1.7.4). *)
Lemma dgpr_adjoint_hom_sub (X X' : Hom V W) :
  dgpr_adjoint_hom (X - X') = dgpr_adjoint_hom X - dgpr_adjoint_hom X'.
Proof.
apply: hom_ext => y; apply: (inner_vectors_ext hB) => x.
rewrite dgpr_hom_subE (dgpr_inner_subr hB) !dgpr_adjoint_homP dgpr_hom_subE.
exact: (dgpr_inner_subl hC).
Qed.

(** Source for [dgpr_square]: X* o X in Hom(V,V), Federer 1.7.4. *)
Definition dgpr_square (X : Hom V W) : Hom V V := hom_comp (dgpr_adjoint_hom X) X.

(** Source for [dgpr_square_symmetric]: X* o X is symmetric, Federer
    1.7.4. *)
Lemma dgpr_square_symmetric (X : Hom V W) : is_symmetric_endomorphism B (hom_as_linear (dgpr_square X)).
Proof.
move=> x y; rewrite !hom_as_linearE /dgpr_square !hom_compE.
by rewrite (inner_symmetric hB) !dgpr_adjoint_homP (inner_symmetric hC).
Qed.

(** Source for [dgpr_Q]: Q = chi^(X* o X), proof of lem:DGPR32 with
    def:spectral. *)
Definition dgpr_Q (X : Hom V W) : Hom V V := dgpr_spectral hB he chi (dgpr_square_symmetric X).

(** Source for [dgpr_square_eigenbasis]: an orthonormal basis of
    eigenvectors of X* o X (Federer 1.7.3); the eigenvalues are
    a_i = |X(u_i)|^2 >= 0 and |X(w)|^2 = sum_i a_i (u_i . w)^2. *)
Lemma dgpr_square_eigenbasis (X : Hom V W) : exists (u : 'I_n -> V) (a : 'I_n -> R),
  [/\ is_basis u, orthonormal_family B u, forall i, dgpr_square X (u i) = a i *: u i,
      forall i, 0 <= a i & forall w, C (X w) (X w) = \sum_i a i * B w (u i) ^+ 2].
Proof.
have [u [a hu]] := symmetric_orthonormal_eigenbasis hB (dgpr_square_symmetric X) he.
have hub := eigenbasis_basis hu; have huo := eigenbasis_orthonormal hu.
have hue : forall i, hom_as_linear (dgpr_square X) (u i) = a i *: u i := eigenbasis_eigenvalue hu.
have hXs : is_adjoint B C (hom_as_linear X) (hom_as_linear (dgpr_adjoint_hom X)).
  by move=> x y; rewrite !hom_as_linearE dgpr_adjoint_homP.
have hue' : forall i, hom_as_linear (dgpr_adjoint_hom X) (hom_as_linear X (u i)) = a i *: u i.
  move=> i; have h := hue i; rewrite hom_as_linearE /dgpr_square hom_compE in h.
  by rewrite !hom_as_linearE.
exists u, a; split.
- exact: hub.
- exact: huo.
- by move=> i; have := hue i; rewrite hom_as_linearE.
- by move=> i; exact: (dgpr_image_eigenvalue_nonnegative hB hC hXs huo hue' i).
- by move=> w; rewrite -hom_as_linearE; exact: (dgpr_image_square hB hXs hub huo hue' w).
Qed.

(** Source for [dgpr_Q_symmetric]: Q is symmetric, def:spectral. *)
Lemma dgpr_Q_symmetric (X : Hom V W) : is_symmetric_endomorphism B (hom_as_linear (dgpr_Q X)).
Proof. exact: dgpr_spectral_symmetric. Qed.

(** Source for [dgpr_Q_image]: proof of lem:DGPR32, eq:32:QB:
    |Q(w)|^2 <= |w|^2 and |Q(w)|^2 <= 16/(3 lambda^2) |X(w)|^2. *)
Lemma dgpr_Q_image (X : Hom V W) (w : V) :
  B (dgpr_Q X w) (dgpr_Q X w) <= B w w /\
  B (dgpr_Q X w) (dgpr_Q X w) <= c * C (X w) (X w).
Proof.
have [u [a [hub huo hue ha hX]]] := dgpr_square_eigenbasis X.
rewrite /dgpr_Q (dgpr_spectral_image_sqr hB he chi (dgpr_square_symmetric X) hub huo hue w).
split.
- rewrite (dgpr_orthonormal_parseval hB hub huo); apply: ler_sum => i _.
  rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r; first exact: sqr_ge0.
  have /andP [h0 h1] := dgpr_chi_range lam (a i).
  by rewrite expr2 -[X in _ <= X]mulr1 ler_pM.
- rewrite hX mulr_sumr; apply: ler_sum => i _; rewrite mulrA.
  apply: ler_wpM2r; first exact: sqr_ge0.
  exact: le_trans (dgpr_chi_sqr_le lam (a i)) (dgpr_chi_le hlam (ha i)).
Qed.

(** Source for [dgpr_Q_operator_norm]: ||Q|| <= 1, Federer 1.7.6. *)
Lemma dgpr_Q_operator_norm (X : Hom V W) : linear_operator_norm hB hB he (hom_as_linear (dgpr_Q X)) <= 1.
Proof.
apply: linear_operator_norm_least => // w; rewrite mul1r hom_as_linearE.
apply: dgpr_sqr_le; first exact: inner_norm_nonnegative.
by rewrite !(inner_norm_sqr hB); have [h _] := dgpr_Q_image X w.
Qed.

(** Source for [dgpr_Q_hom_norm_lower]: |Q|^2 = sum_i chi(a_i)^2, and
    |Q|^2 >= m when sv_m(X) >= lambda/2 (lem:sv, item eigen, and
    chi = 1 on [lambda^2/4, infinity)); proof of lem:DGPR32. *)
Lemma dgpr_Q_hom_norm_lower (X : Hom V W) :
  lam / 2 <= dgpr_sv hB hC he hm X -> m%:R <= HV (dgpr_Q X) ^+ 2.
Proof.
move=> hsv.
have [u [a [hub huo hue ha hX]]] := dgpr_square_eigenbasis X.
rewrite /dgpr_Q (dgpr_spectral_hom_norm_sqr hB he chi (dgpr_square_symmetric X) hub huo hue).
have hue' i : inner_adjoint hB hC he (hom_as_linear X) (X (u i)) = a i *: u i.
  by rewrite -hue /dgpr_square hom_compE /dgpr_adjoint_hom hom_of_linearE.
have hcard := dgpr_sv_eigen (a0 := lam / 2) (divr_gt0 hlam (ltr0Sn R 1)) hsv hub huo hue'.
have e2 : (lam / 2) ^+ 2 = lam ^+ 2 / 4 by rewrite expr_div_n; congr (_ / _); rewrite expr2 -natrM.
rewrite e2 in hcard.
apply: le_trans (_ : #|[set i : 'I_n | lam ^+ 2 / 4 <= a i]|%:R <= _).
  by rewrite ler_nat.
rewrite -sum1_card natr_sum [X in _ <= X](bigID (fun i => i \in [set i : 'I_n | lam ^+ 2 / 4 <= a i])) /=.
rewrite -[X in X <= _]addr0; apply: lerD.
  by apply: ler_sum => i; rewrite inE => hi; rewrite dgpr_chi_one // expr1n.
by apply: sumr_ge0 => i _; exact: sqr_ge0.
Qed.

(** Source for [dgpr_square_lipschitz]: |X* o X - X'* o X'| <=
    (|X| + |X'|) |X - X'|, from X* o X - X'* o X' =
    X* o (X - X') + (X - X')* o X', |L o A| <= ||L|| |A|, ||L|| <= |L| and
    |A*| = |A| (Federer 1.7.4, 1.7.6, 1.7.9; DgprHomNorms.v). *)
Lemma dgpr_square_lipschitz (X X' : Hom V W) :
  HV (dgpr_square X - dgpr_square X') <= (HX X + HX X') * HX (X - X').
Proof.
have e1 : dgpr_square X - dgpr_square X' =
    hom_comp (dgpr_adjoint_hom X) (X - X') + hom_comp (dgpr_adjoint_hom (X - X')) X'.
  apply: hom_ext => v; rewrite dgpr_adjoint_hom_sub /dgpr_square.
  rewrite !(hom_addE, dgpr_hom_subE, hom_compE).
  by rewrite linearB /= addrA subrK.
have ht := inner_norm_triangle (hom_inner_productP hB hB he)
  (hom_comp (dgpr_adjoint_hom X) (X - X')) (hom_comp (dgpr_adjoint_hom (X - X')) X').
rewrite e1; apply: le_trans ht _.
have hadj (A : Hom V W) : linear_operator_norm hC hB hf (hom_as_linear (dgpr_adjoint_hom A)) <= HX A.
  have h := operator_norm_le_hom_norm hf
    (linear_operator_normP hC hB hf (hom_as_linear (dgpr_adjoint_hom A))).
  by rewrite /dgpr_adjoint_hom (dgpr_hom_norm_adjoint hB hC he hf) in h.
have h1 := dgpr_hom_norm_comp_left hB hC hB he hf (X - X') (dgpr_adjoint_hom X).
have h2 := dgpr_hom_norm_comp_left hB hC hB he hf X' (dgpr_adjoint_hom (X - X')).
rewrite mulrDl; apply: lerD.
- apply: le_trans h1 _; apply: ler_wpM2r; first exact: inner_norm_nonnegative.
  exact: hadj.
- rewrite [X in _ <= X]mulrC; apply: le_trans h2 _.
  apply: ler_wpM2r; first exact: inner_norm_nonnegative.
  exact: hadj.
Qed.

(** Source for [dgpr_Q_lipschitz]: lem:spectral with eq:32:chi:
    |Q(X) - Q(X')| <= 16/(3 lambda^2) (|X| + |X'|) |X - X'|. *)
Lemma dgpr_Q_lipschitz (X X' : Hom V W) :
  HV (dgpr_Q X - dgpr_Q X') <= c * ((HX X + HX X') * HX (X - X')).
Proof.
apply: le_trans (dgpr_spectral_lipschitz hB he (dgpr_square_symmetric X) (dgpr_square_symmetric X')
  (dgpr_chi_lipschitz hlam)) _.
apply: ler_wpM2l; first exact: ltW (dgpr_chi_constant_gt0 hlam).
exact: dgpr_square_lipschitz.
Qed.
End Spectral.
