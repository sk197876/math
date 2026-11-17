(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: nonzero power determinant makes
    the original element primitive. Apply the
    determinant formula and finite-dimensional inverse
    theorem already proved in Chapters 1 and 2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp fingroup perm.
From Federer Require Import TensorUP Hom LinearBasis Annihilator FiniteDualDimension
  ExteriorDeterminant ExteriorLeibniz InversionCount HomHaarCovariance LinearGroupTopology
  RingScalarRestriction CommutativePolynomialUP CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section PowerFamilies.
Variables K L:fieldType.
Variable phi:{rmorphism K->L}.
Local Notation V:=[the lmodType K of ring_restricted_space phi L^o].
Variable d:nat.
Variable basis:'I_d->V.
Hypothesis hBasis:is_basis basis.
Hypothesis hTwo:(1+1:K)!=0.

(** Source for [power_family_determinant_comparison]: the
    coefficient determinant of the original power
    family is the intrinsic determinant of
    its basis map, by 1.3.4, p. 16,
    supporting the simplicity assertion in 3.4.8(8), p. 330. *)
Lemma power_family_determinant_comparison (z:L) (T:{linear V->V}):
  (forall i:'I_d,T (basis i) = z^+(i:nat)) ->
  det hTwo hBasis T = \sum_(sigma:'S_d) FedererPermutation.index K sigma *
    \prod_(i<d) dual_basis hBasis (sigma i) (z^+(i:nat)).
Proof.
move=>hT;apply:(@det_formula K hTwo d V basis hBasis T
  (fun i j=>dual_basis hBasis j (z^+(i:nat))))=>i.
rewrite hT;exact:basis_vector_expansion hBasis (z^+(i:nat)).
Qed.

(** Source for [power_family_nonzero_determinant_generates]:
    invertibility of the power-basis map gives
    an original polynomial expression for every
    element, supporting the primitive-element step
    in 3.4.8(8), p. 330. Apply existing
    determinant and finite-dimensional inverse results. *)
Theorem power_family_nonzero_determinant_generates (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (z:L) (E:{rmorphism B->L}):
  is_commutative_polynomial_evaluation embed variable phi z E ->
  (\sum_(sigma:'S_d) FedererPermutation.index K sigma *
    \prod_(i<d) dual_basis hBasis (sigma i) (z^+(i:nat)))<>0 ->
  forall y:L,exists P:B,E P = y.
Proof.
move=>hE hNonzero y.
pose powers:=fun i:'I_d=>(z^+(i:nat):V).
pose T:=linear_comp (basis_synthesis powers) (basis_coordinates hBasis).
have hT i:T (basis i) = z^+(i:nat).
  change (basis_synthesis powers (basis_coordinates hBasis (basis i)) = powers i).
  by rewrite basis_coordinatesE basis_synthesisE.
have hDet:det hTwo hBasis T!=0.
  apply/eqP;rewrite (power_family_determinant_comparison hT);exact:hNonzero.
have hInjective:injective T:=(det_nonzero_injective hTwo hBasis T).1 hDet.
have [u hU]:=finite_injective_surjective hBasis hInjective y.
exists (\sum_(i<d) embed (dual_basis hBasis i u)*variable^+(i:nat)).
rewrite rmorph_sum.
under eq_bigr do rewrite rmorphM rmorphXn (polynomial_evaluation_constants hE)
  (polynomial_evaluation_variable hE).
rewrite -hU {2}(basis_vector_expansion hBasis u) linear_sum.
apply:eq_bigr=>i _;rewrite linearZ hT;reflexivity.
Qed.

(** Source for [power_family_basis_determinant_one]: the
    power determinant is one at an original
    element whose powers are the selected basis,
    by the identity determinant in 1.3.4,
    p. 16, supporting 3.4.8(8), p. 330. *)
Theorem power_family_basis_determinant_one (z:L):
  (forall i:'I_d,basis i = z^+(i:nat)) ->
  (\sum_(sigma:'S_d) FedererPermutation.index K sigma *
    \prod_(i<d) dual_basis hBasis (sigma i) (z^+(i:nat))) = 1.
Proof.
move=>hBasisValues.
have hIdentity i:linear_id V (basis i) = z^+(i:nat):=hBasisValues i.
rewrite -(power_family_determinant_comparison hIdentity).
exact:(@ExteriorDeterminant.det_id K hTwo d V basis hBasis).
Qed.
End PowerFamilies.
