(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    def:spectral: existence of chi^(A) for a symmetric endomorphism A of
    a finite dimensional inner product space V. With an orthonormal basis
    of eigenvectors u_i and eigenvalues a_i from Federer 1.7.3, the map
    sum_i chi(a_i) (u_i . _) u_i has the characteristic property, because
    (a_i - a)(u_i . v) = 0 whenever A(v) = a v. Private: later files use
    DgprSpectralCalculus.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Bilinear InnerProductUP InnerProductLaws LinearBasis Hom
  OrthonormalFamilies SymmetricEndomorphisms EigenbasisUP SymmetricEigenbasis
  CoefficientCoordinates.
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprSpectralCalculusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dgpr_spectral_value_exists]: blueprint def:spectral,
    existence of chi^(A) from an orthonormal basis of eigenvectors of A
    (Federer 1.7.3, p. 29). *)
Theorem dgpr_spectral_value_exists (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    (chi : R -> R) (A : Hom V V) (hA : is_symmetric_endomorphism B (hom_as_linear A)) :
  exists F : Hom V V, is_dgpr_spectral_value chi A F.
Proof.
have [u [a hu]] := symmetric_orthonormal_eigenbasis hB hA he.
have hub := eigenbasis_basis hu; have huo := eigenbasis_orthonormal hu.
have hue : forall i, A (u i) = a i *: u i := eigenbasis_eigenvalue hu.
pose F := \sum_i chi (a i) *: dgpr_rank_one (hom_of_linear (inner_coordinate hB (u i))) (u i).
exists F => c v hv.
have hFv : F v = \sum_i (chi (a i) * B v (u i)) *: u i.
  rewrite dgpr_hom_sum_apply; apply: eq_bigr => i _.
  by rewrite hom_scaleE dgpr_rank_oneE hom_of_linearE inner_coordinateE scalerA.
have hcoef i : chi (a i) * B v (u i) = chi c * B v (u i).
  have h1 : B (A v) (u i) = a i * B v (u i).
    have := hA v (u i); rewrite !hom_as_linearE => ->.
    by rewrite hue dgpr_innerZr.
  have h2 : B (A v) (u i) = c * B v (u i) by rewrite hv dgpr_innerZl.
  have [hz|hz] := eqVneq (B v (u i)) 0; first by rewrite hz !mulr0.
  have hac : a i = c by apply: (mulIf hz); rewrite -h1 -h2.
  by rewrite hac.
rewrite hFv {2}(dgpr_orthonormal_expansion hB hub huo v) scaler_sumr.
by apply: eq_bigr => i _; rewrite hcoef scalerA.
Qed.
