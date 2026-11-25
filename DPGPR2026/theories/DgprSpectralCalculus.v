(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:spectral and lem:spectral: the public map chi^(A) for chi : R -> R
    and a symmetric endomorphism A of a finite dimensional inner product
    space V, its formula in every orthonormal basis of eigenvectors, its
    symmetry, the location of its eigenvalues, and the Lipschitz estimate
    |chi^(A) - chi^(A')| <= Lip(chi) |A - A'| for the norm of Federer
    1.7.9. All proofs use the sealed characteristic property. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp topology.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerProductLaws InnerNorm
  LinearBasis Hom HomInner OrthonormalFamilies SymmetricEndomorphisms EigenbasisUP
  SymmetricEigenbasis LipschitzUP LipschitzConstant RealMetricBackground.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprSpectralCalculusUP
  DgprSpectralCalculusSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Interface.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [dgpr_spectral]: blueprint def:spectral, the map
    chi^(A), read from the sealed interface. *)
Definition dgpr_spectral (chi : R -> R) (A : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A)) : Hom V V :=
  @DgprSpectralCalculus.value R V B hB n e he chi A hA.

Variable chi : R -> R.

(** Source for [dgpr_spectralP]: blueprint def:spectral, chi^(A) acts
    by chi(a) on ker(A - a 1_V) for every a in R. *)
Theorem dgpr_spectralP (A : Hom V V) (hA : is_symmetric_endomorphism B (hom_as_linear A)) :
  is_dgpr_spectral_value chi A (dgpr_spectral chi hA).
Proof. exact: DgprSpectralCalculus.laws. Qed.

(** Source for [dgpr_spectral_characterisation]: blueprint
    def:spectral, every endomorphism with the characteristic property is
    chi^(A). *)
Lemma dgpr_spectral_characterisation (A F : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A)) :
  is_dgpr_spectral_value chi A F -> dgpr_spectral chi hA = F.
Proof. move=> hF; exact: dgpr_spectral_value_unique he hA (dgpr_spectralP hA) hF. Qed.

(** Source for [dgpr_spectral_expansion]: blueprint def:spectral, the
    displayed formula chi^(A)(v) = sum_i chi(a_i) (u_i . v) u_i for
    every orthonormal basis u_1, ..., u_k of eigenvectors of A. *)
Theorem dgpr_spectral_expansion (A : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A))
    k (u : 'I_k -> V) (a : 'I_k -> R) :
  is_basis u -> orthonormal_family B u -> (forall i, A (u i) = a i *: u i) ->
  forall v, dgpr_spectral chi hA v = \sum_i (chi (a i) * B v (u i)) *: u i.
Proof. move=> hu ho hAu v; exact: (dgpr_spectral_value_expansion hB (dgpr_spectralP hA) hu ho hAu v). Qed.

(** Source for [dgpr_spectral_symmetric]: blueprint lem:spectral, first
    assertion: chi^(A) is a symmetric endomorphism. *)
Theorem dgpr_spectral_symmetric (A : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A)) :
  is_symmetric_endomorphism B (hom_as_linear (dgpr_spectral chi hA)).
Proof.
have [u [a hu]] := symmetric_orthonormal_eigenbasis hB hA he.
exact: (dgpr_spectral_value_symmetric hB (dgpr_spectralP hA)
  (eigenbasis_basis hu) (eigenbasis_orthonormal hu) (eigenbasis_eigenvalue hu)).
Qed.

(** Source for [dgpr_spectral_eigenvalue]: blueprint lem:spectral,
    second assertion: every eigenvalue c of chi^(A) belongs to
    chi[{ a : ker(A - a 1_V) <> {0} }]. *)
Theorem dgpr_spectral_eigenvalue (A : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A)) c v :
  v != 0 -> dgpr_spectral chi hA v = c *: v ->
  exists a, (exists w, w != 0 /\ A w = a *: w) /\ c = chi a.
Proof.
move=> hv hFv.
have [u [a hu]] := symmetric_orthonormal_eigenbasis hB hA he.
have huo := eigenbasis_orthonormal hu.
have [i hi] := dgpr_spectral_value_eigenvalue hB (dgpr_spectralP hA)
  (eigenbasis_basis hu) huo (eigenbasis_eigenvalue hu) hv hFv.
exists (a i); split=> //; exists (u i); split; last exact: (eigenbasis_eigenvalue hu i).
apply/negP => /eqP h0; have := orthonormal_diagonal huo i.
by rewrite h0 -(inner_coordinateE hB) linear0 => /eqP; rewrite eq_sym oner_eq0.
Qed.

(** Source for [dgpr_spectral_image_sqr]: blueprint proof of lem:DGPR32,
    display (eq:32:QB): |chi^(A)(w)|^2 = sum_i chi(a_i)^2 (u_i . w)^2. *)
Lemma dgpr_spectral_image_sqr (A : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A))
    k (u : 'I_k -> V) (a : 'I_k -> R) :
  is_basis u -> orthonormal_family B u -> (forall i, A (u i) = a i *: u i) ->
  forall w, B (dgpr_spectral chi hA w) (dgpr_spectral chi hA w) =
    \sum_i chi (a i) ^+ 2 * B w (u i) ^+ 2.
Proof.
move=> hu ho hAu w; rewrite (dgpr_orthonormal_parseval hB hu ho); apply: eq_bigr => i _.
by rewrite (dgpr_spectral_value_coefficient hB (dgpr_spectralP hA) hu ho hAu) exprMn.
Qed.

(** Source for [dgpr_spectral_hom_norm_sqr]: blueprint proof of
    lem:DGPR32: |chi^(A)|^2 = sum_i chi(a_i)^2 (Federer 1.7.9). *)
Lemma dgpr_spectral_hom_norm_sqr (A : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A))
    k (u : 'I_k -> V) (a : 'I_k -> R) :
  is_basis u -> orthonormal_family B u -> (forall i, A (u i) = a i *: u i) ->
  hom_norm hB hB he (dgpr_spectral chi hA) ^+ 2 = \sum_i chi (a i) ^+ 2.
Proof.
move=> hu ho hAu; rewrite (dgpr_hom_norm_sqr hB hB he _ hu ho); apply: eq_bigr => i _.
rewrite (dgpr_spectral_value_eigenvector (dgpr_spectralP hA) hAu i).
by rewrite dgpr_innerZl // dgpr_innerZr // (orthonormal_diagonal ho) mulr1 expr2.
Qed.
End Interface.

Section Lipschitz.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [dgpr_spectral_difference_sqr]: blueprint proof of
    lem:spectral: if G and G' are the spectral values of A and A' for chi,
    and u, u' are orthonormal bases of eigenvectors of A, A' with
    eigenvalues a, a', then
    |G - G'|^2 = sum_(i,j) (chi(a_i) - chi(a'_j))^2 (u_i . u'_j)^2.
    This is the blueprint's sum over the products pi_i o pi'_j, with
    |pi_i o pi'_j|^2 = (u_i . u'_j)^2. *)
Lemma dgpr_spectral_difference_sqr (chi : R -> R) (A A' G G' : Hom V V)
    k (u : 'I_k -> V) (a : 'I_k -> R) l (u' : 'I_l -> V) (a' : 'I_l -> R) :
  is_dgpr_spectral_value chi A G -> is_dgpr_spectral_value chi A' G' ->
  is_basis u -> orthonormal_family B u -> (forall i, A (u i) = a i *: u i) ->
  is_basis u' -> orthonormal_family B u' -> (forall j, A' (u' j) = a' j *: u' j) ->
  hom_norm hB hB he (G - G') ^+ 2 =
    \sum_j \sum_i ((chi (a i) - chi (a' j)) * B (u' j) (u i)) ^+ 2.
Proof.
move=> hG hG' hu ho hAu hu' ho' hAu'.
rewrite (dgpr_hom_norm_sqr hB hB he _ hu' ho'); apply: eq_bigr => j _.
rewrite (dgpr_orthonormal_parseval hB hu ho); apply: eq_bigr => i _.
congr (_ ^+ 2).
have hsub : (G - G') (u' j) = G (u' j) - G' (u' j) by [].
have hBl x y : B (x - y) (u i) = B x (u i) - B y (u i).
  by rewrite -!(inner_coordinateE hB) linearB.
rewrite hsub hBl (dgpr_spectral_value_coefficient hB hG hu ho hAu).
by rewrite (dgpr_spectral_value_eigenvector hG' hAu' j) dgpr_innerZl // mulrBl.
Qed.

(** Source for [dgpr_spectral_lipschitz]: blueprint lem:spectral,
    displayed estimate: if |chi(x) - chi(y)| <= L |x - y| for x, y in R,
    then |chi^(A) - chi^(A')| <= L |A - A'| for symmetric A, A', with the
    norm |.| of Federer 1.7.9. *)
Theorem dgpr_spectral_lipschitz (chi : R -> R) (L : R) (A A' : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A))
    (hA' : is_symmetric_endomorphism B (hom_as_linear A')) :
  (forall x y, `|chi x - chi y| <= L * `|x - y|) ->
  hom_norm hB hB he (dgpr_spectral hB he chi hA - dgpr_spectral hB he chi hA') <=
    L * hom_norm hB hB he (A - A').
Proof.
move=> hchi.
have hL : 0 <= L.
  have := hchi 1 0; rewrite subr0 normr1 mulr1; exact: le_trans (normr_ge0 _).
have [u [a hu]] := symmetric_orthonormal_eigenbasis hB hA he.
have [u' [a' hu']] := symmetric_orthonormal_eigenbasis hB hA' he.
have hub := eigenbasis_basis hu; have huo := eigenbasis_orthonormal hu.
have hue : forall i, A (u i) = a i *: u i := eigenbasis_eigenvalue hu.
have hub' := eigenbasis_basis hu'; have huo' := eigenbasis_orthonormal hu'.
have hue' : forall j, A' (u' j) = a' j *: u' j := eigenbasis_eigenvalue hu'.
apply: dgpr_sqr_le; first by rewrite mulr_ge0 // inner_norm_nonnegative.
rewrite exprMn (dgpr_spectral_difference_sqr (@dgpr_spectralP R V B hB n e he chi A hA) (@dgpr_spectralP R V B hB n e he chi A' hA')
  hub huo hue hub' huo' hue').
rewrite (dgpr_spectral_difference_sqr (dgpr_spectral_value_self (A:=A)) (dgpr_spectral_value_self (A:=A'))
  hub huo hue hub' huo' hue').
have hterm x y : (chi x - chi y) ^+ 2 <= L ^+ 2 * (x - y) ^+ 2.
  rewrite -exprMn -(real_normK (num_real (chi x - chi y))) -(real_normK (num_real (L * (x - y)))).
  apply: lerXn2r; rewrite ?nnegrE ?normr_ge0 //.
  by rewrite normrM (ger0_norm hL); exact: hchi.
rewrite mulr_sumr; apply: ler_sum => j _; rewrite mulr_sumr; apply: ler_sum => i _.
rewrite !exprMn mulrA; apply: ler_wpM2r; first exact: sqr_ge0.
exact: hterm.
Qed.

(** Source for [dgpr_spectral_lipschitz_constant]: blueprint
    lem:spectral, displayed estimate with Lip(chi) of Federer 2.2.7,
    p. 64, for the metric of the real line:
    |chi^(A) - chi^(A')| <= Lip(chi) |A - A'|. *)
Theorem dgpr_spectral_lipschitz_constant (chi : R -> R)
    (hchi : is_metric_lipschitz (setT : set (real_line_metric R))
      (chi : real_line_metric R -> real_line_metric R))
    (A A' : Hom V V)
    (hA : is_symmetric_endomorphism B (hom_as_linear A))
    (hA' : is_symmetric_endomorphism B (hom_as_linear A')) :
  hom_norm hB hB he (dgpr_spectral hB he chi hA - dgpr_spectral hB he chi hA') <=
    metric_lipschitz_constant hchi * hom_norm hB hB he (A - A').
Proof.
apply: dgpr_spectral_lipschitz => x y.
have := @metric_lipschitz_constant_attained R _ _ _ _ hchi x y I I.
by rewrite !real_line_metric_distanceE.
Qed.
End Lipschitz.
