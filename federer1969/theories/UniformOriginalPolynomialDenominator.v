(** Federer (1969), 3.4.8(10), p. 331:
    all original polynomial relations use
    one common original denominator, retaining
    the same degree bound. Apply the
    proved finite common multiple and
    original ideal absorption laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets ring.
From Federer Require Import CommutativeDomainUP CommutativeIdealUP FractionFieldUP
  CommutativePolynomialUP CommutativePolynomialBasicLaws PolynomialCoefficientDivision CommutativePolynomialEvaluationUP
  FiniteOriginalCommonMultiple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_original_polynomial_denominator]:
    replacing each delta_j by one common
    delta changes only its bounded polynomial
    numerator, 3.4.8(10), p. 331.
    Coefficient scalar multiplication preserves the
    original support, and ideal absorption
    preserves each original relation. *)
Theorem uniform_original_polynomial_denominator (A P G:comNzRingType) (M:fieldType)
  (embed:{rmorphism A->P}) (variable:P) (coefficient:P->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (E:{rmorphism A->G}) (gamma:G) (J:{rmorphism P->G})
  (eta:{rmorphism A->M}) (hField:is_commutative_fraction_field eta)
  (hDomain:is_commutative_integral_domain A) (I:set G) N k
  (d:'I_N->A) (T:'I_N->P) (sigma:'I_N->G):
  is_commutative_ideal I ->is_commutative_polynomial_evaluation embed variable E gamma J ->
  (forall i,eta (d i)<>0) ->
  (forall i j,(k<=j)%N ->coefficient (T i) j = 0) ->
  (forall i,I (E (d i)*sigma i-J (T i))) ->
  exists delta:A,eta delta<>0 /\forall i:'I_N,exists Q:P,
    (forall j,(k<=j)%N ->coefficient Q j = 0) /\I (E delta*sigma i-J Q).
Proof.
move=>hI hJ hNonzero hSupport hRelations.
have [delta [hDelta hMultipliers]]:=@finite_original_nonzero_common_multiple A M eta hField hDomain N d hNonzero.
exists delta;split;first exact:hDelta.
move=>i;have [a hA]:=hMultipliers i.
exists (embed a*T i);split.
- move=>j hJBound;by rewrite (@polynomial_coefficient_scalar_multiply A P embed variable coefficient hP)
    hSupport // mulr0.
- have hRelation:=@commutative_ideal_mul G I hI (E a) (E (d i)*sigma i-J (T i)) (hRelations i).
  have hEquation:E delta*sigma i-J (embed a*T i) = E a*(E (d i)*sigma i-J (T i)).
    rewrite hA !rmorphM (polynomial_evaluation_constants hJ).
    ring.
  by rewrite hEquation.
Qed.
