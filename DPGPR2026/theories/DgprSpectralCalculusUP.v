(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:spectral: for chi : R -> R and a symmetric endomorphism A of a
    finite dimensional inner product space V, the map chi^(A) acts by
    chi(a) on each eigenspace ker(A - a 1_V). This file states that
    characteristic property and derives from it, for any orthonormal
    basis of eigenvectors u_i of A with eigenvalues a_i (Federer 1.7.3),
    the formula chi^(A)(v) = sum_i chi(a_i) (u_i . v) u_i of def:spectral,
    the symmetry of chi^(A), the location of its eigenvalues, and
    uniqueness. The map is chosen in DgprSpectralCalculusSealed.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerProductLaws LinearBasis Hom
  OrthonormalFamilies SymmetricEndomorphisms EigenbasisUP SymmetricEigenbasis.
From DPGPR Require Import DgprOrthonormalCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Predicate.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [is_dgpr_spectral_value]: blueprint def:spectral, last
    sentence: F acts by chi(a) on ker(A - a 1_V) for every a in R, that
    is, F(v) = chi(a) v whenever A(v) = a v. *)
Definition is_dgpr_spectral_value (chi : R -> R) (A F : Hom V V) : Prop :=
  forall (a : R) v, A v = a *: v -> F v = chi a *: v.

(** Source for [dgpr_spectral_value_self]: blueprint lem:spectral,
    proof: A itself is the spectral value of A for the identity map. *)
Lemma dgpr_spectral_value_self (A : Hom V V) : is_dgpr_spectral_value id A A.
Proof. by move=> a v. Qed.

Section Eigenbasis.
Variable chi : R -> R.
Variables A F : Hom V V.
Hypothesis hF : is_dgpr_spectral_value chi A F.
Variable k : nat.
Variable u : 'I_k -> V.
Variable a : 'I_k -> R.
Hypothesis hu : is_basis u.
Hypothesis ho : orthonormal_family B u.
Hypothesis hA : forall i, A (u i) = a i *: u i.

(** Source for [dgpr_spectral_value_eigenvector]: blueprint
    def:spectral, chi^(A)(u_i) = chi(a_i) u_i. *)
Lemma dgpr_spectral_value_eigenvector i : F (u i) = chi (a i) *: u i.
Proof. exact: hF (hA i). Qed.

(** Source for [dgpr_spectral_value_expansion]: blueprint
    def:spectral, the displayed formula
    chi^(A)(v) = sum_i chi(a_i) (u_i . v) u_i for every orthonormal basis
    of eigenvectors; hence the definition does not depend on the basis. *)
Lemma dgpr_spectral_value_expansion v : F v = \sum_i (chi (a i) * B v (u i)) *: u i.
Proof.
exact: (@dgpr_eigen_expansion R V B hB _ u hu ho (hom_as_linear F) (fun i => chi (a i))
  dgpr_spectral_value_eigenvector v).
Qed.

(** Source for [dgpr_spectral_value_coefficient]: blueprint
    def:spectral, chi^(A)(v) . u_i = chi(a_i) (v . u_i). *)
Lemma dgpr_spectral_value_coefficient v i : B (F v) (u i) = chi (a i) * B v (u i).
Proof. by rewrite dgpr_spectral_value_expansion dgpr_orthonormal_coefficient. Qed.

(** Source for [dgpr_spectral_value_symmetric]: blueprint
    lem:spectral, first assertion: chi^(A) is symmetric. *)
Lemma dgpr_spectral_value_symmetric : is_symmetric_endomorphism B (hom_as_linear F).
Proof.
move=> x y; rewrite !hom_as_linearE (dgpr_orthonormal_inner hB hu ho (F x) y).
rewrite (dgpr_orthonormal_inner hB hu ho x (F y)); apply: eq_bigr => i _.
by rewrite !dgpr_spectral_value_coefficient mulrCA mulrA.
Qed.

(** Source for [dgpr_spectral_value_eigenvalue]: blueprint
    lem:spectral, second assertion: if chi^(A)(v) = c v with v nonzero,
    then c = chi(a_i) for some eigenvalue a_i of A. *)
Lemma dgpr_spectral_value_eigenvalue c v :
  v != 0 -> F v = c *: v -> exists i, c = chi (a i).
Proof.
move=> hv hFv.
have [i hi] : exists i, B v (u i) != 0.
  case: (pselect (exists i, B v (u i) != 0)) => // hn; exfalso.
  move/eqP: hv; apply; apply: (dgpr_orthonormal_zero hB hu ho) => i.
  by apply/eqP/negPn/negP => hi; apply: hn; exists i.
exists i; apply: (mulIf hi).
by rewrite -dgpr_spectral_value_coefficient hFv dgpr_innerZl.
Qed.
End Eigenbasis.

(** Source for [dgpr_spectral_value_unique]: blueprint def:spectral, at
    most one endomorphism has the characteristic property, since V has an
    orthonormal basis of eigenvectors of A by Federer 1.7.3. *)
Lemma dgpr_spectral_value_unique n (e : 'I_n -> V) (chi : R -> R) (A F G : Hom V V) :
  is_basis e -> is_symmetric_endomorphism B (hom_as_linear A) ->
  is_dgpr_spectral_value chi A F -> is_dgpr_spectral_value chi A G -> F = G.
Proof.
move=> he hA hF hG.
have [u [a hu]] := symmetric_orthonormal_eigenbasis hB hA he.
have hub := eigenbasis_basis hu; have huo := eigenbasis_orthonormal hu.
have hue : forall i, A (u i) = a i *: u i := eigenbasis_eigenvalue hu.
apply: hom_ext => v.
by rewrite (dgpr_spectral_value_expansion hF hub huo hue)
  (dgpr_spectral_value_expansion hG hub huo hue).
Qed.
End Predicate.
