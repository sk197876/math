(** Federer (1969), 4.1.25, p. 383: pointwise
    laws for the target-form area auxiliary, by the
    preceding fixed-covector laws at a=phi(f(x)).
    This does not change the original vector domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  EuclideanLinearJacobian PartialFunctionUP
  CurrentAreaNormalisedImageSealed CurrentAreaPairingQuotientUP
  CurrentAreaPairingQuotientSealed CurrentAreaPairingQuotientLaws
  CurrentAreaPairingQuotientTestUP CurrentAreaPairingQuotientTestSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section TargetFormAreaQuotient.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Variables (f:X->Y) (xi:X->exterior_power X m) (phi:Y->A_m Y R^o m).
Local Notation q:=(@CurrentAreaPairingQuotientTest.value R m n f xi phi).

(** Source for [current_area_pairing_quotient_test_fixed_graph]:
    evaluate the scalar pairing at phi(f(x)) in
    the area proof of 4.1.25, p. 383. *)
Lemma current_area_pairing_quotient_test_fixed_graph x z:
  partial_function_graph q x z <->
  partial_function_graph
    (@CurrentAreaPairingQuotient.value R m n f xi (phi (f x))) x z.
Proof.
by rewrite (@CurrentAreaPairingQuotientTest.laws R m n f xi phi x z)
  (@CurrentAreaPairingQuotient.laws R m n f xi (phi (f x)) x z).
Qed.

(** Source for [current_area_pairing_quotient_test_at_differential]:
    every original differential gives its variable-form
    scalar auxiliary in 4.1.25, p. 383. *)
Lemma current_area_pairing_quotient_test_at_differential x (D:Hom X Y):
  has_norm_differential NX NY setT f x D ->
  partial_function_graph q x
    (current_area_pairing_quotient_coefficient xi (phi (f x)) x D)%:E.
Proof.
move=>hD;apply:(current_area_pairing_quotient_test_fixed_graph x _).2.
exact:(@current_area_pairing_quotient_at_differential R m n f xi (phi (f x)) x D hD).
Qed.

(** Source for [current_area_pairing_quotient_test_domain]:
    the auxiliary retains the full differential domain
    of the first display of 4.1.25, p. 383,
    including differential points of zero Jacobian. *)
Theorem current_area_pairing_quotient_test_domain x:
  partial_function_domain q x <-> norm_differentiable_at NX NY setT f x.
Proof.
split.
- move=>[z hZ].
  have hFixed:=(current_area_pairing_quotient_test_fixed_graph x z).1 hZ.
  apply:(@current_area_pairing_quotient_domain R m n f xi (phi (f x)) x).1.
  by exists z.
- move=>[D hD].
  exists (current_area_pairing_quotient_coefficient xi (phi (f x)) x D)%:E.
  exact:current_area_pairing_quotient_test_at_differential hD.
Qed.

(** Source for [current_area_pairing_quotient_test_critical]:
    scalar zero at a critical differential in the
    auxiliary of 4.1.25, p. 383. The original
    vector summand remains undefined there. *)
Lemma current_area_pairing_quotient_test_critical x (D:Hom X Y):
  has_norm_differential NX NY setT f x D ->
  @euclidean_linear_jacobian R m n m D=0 ->
  partial_function_graph q x 0%E.
Proof.
move=>hD hZero;apply:(current_area_pairing_quotient_test_fixed_graph x _).2.
exact:(@current_area_pairing_quotient_critical R m n f xi (phi (f x)) x D hD hZero).
Qed.

(** Source for [current_area_pairing_quotient_test_normalised_value]:
    at every original normalized summand, pair with
    the actual phi(f(x)) in 4.1.25, p. 383. *)
Theorem current_area_pairing_quotient_test_normalised_value x v:
  partial_function_graph (@CurrentAreaNormalisedImage.value R m n f xi) x v ->
  partial_function_graph q x (pairing v (phi (f x)))%:E.
Proof.
move=>hV;apply:(current_area_pairing_quotient_test_fixed_graph x _).2.
exact:(@current_area_pairing_quotient_normalised_value R m n f xi (phi (f x)) x v hV).
Qed.
End TargetFormAreaQuotient.
