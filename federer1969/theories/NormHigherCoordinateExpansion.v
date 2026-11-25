(** Federer (1969), 3.1.11, p. 223: the full
    coordinate expansion of the actual kth differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  SymmetricForms SymmetricFormExtension SymmetricMultiIndices SymmetricIndexBounds
  SymmetricDividedMonomials SymmetricMonomialTuples SymmetricCoordinateDualBasis SymmetricFormCoordinateExpansion
  ContinuousMultilinearUP NormHigherSymmetricFormUP NormHigherMultiPartialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_coordinate_expansion]: the displayed
    sum D^k f(a)=sum_alpha D^alpha f(a) omega^alpha/alpha!
    in Federer 3.1.11, p. 223. Every coefficient is
    required to belong to the exact multi-partial graph.
    The equality includes degree zero and zero-dimensional source. *)
Theorem norm_higher_coordinate_expansion (R : realType) n (Y : lmodType R)
    (NX : R_n R n->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R n}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : R_n R n->Prop) (f : R_n R n->Y) k a
    (phi : S_m (R_n R n) Y k) (c : symmetric_indices n k->Y) :
  is_norm_higher_differential_form NX ev ZN A f k a phi ->
  (forall alpha, has_norm_multi_partial NX ev ZN A f alpha a (c alpha)) ->
  forall t : k.-tuple (R_n R n),
    phi t=\sum_(alpha : symmetric_indices n k)
      ((symmetric_multi_factorial (symmetric_indices_unbound alpha))%:R)^-1*:
        ((symmetric_coordinate_basis_form (@coordinate_basisP R n) k alpha t : R)*:
          c alpha).
Proof.
move=>hphi hc t.
rewrite (@symmetric_form_coordinate_expansion R (pchar_num R)
  (R_n R n) Y n (@coordinate_basis R n) (@coordinate_basisP R n) k phi t).
apply: eq_bigr=>alpha _.
have he := @norm_multi_partial_unique R n Y NX NY hNX hNY Z ev ZN hZ
  A f k alpha a _ _ (norm_multi_partial_form_evaluation alpha hphi) (hc alpha).
by rewrite symmetric_monomial_form_value in he; rewrite he.
Qed.
