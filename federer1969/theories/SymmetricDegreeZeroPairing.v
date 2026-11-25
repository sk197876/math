(** Federer (1969), 1.10.5, pp. 47-48: degree-zero interpretation of the
    norm definitions, using the identifications in 1.9.1, p. 41, and 1.10.1,
    p. 44. The scalar pairing is established separately here. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP AlgebraUP Bilinear Graded GradedComponents
  SymmetricAlgebra SymmetricGrading SymmetricLowPowers SymmetricForms
  SymmetricFormIsomorphism SymmetricPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_zeroth_tuple_scalar]: Federer 1.10.5,
    p. 48, supporting zero-degree convention: an included scalar
    is that scalar times the empty product. *)
Lemma symmetric_zeroth_tuple_scalar (K : fieldType) (V : lmodType K) (c : K) :
  symmetric_zeroth_inclusion V c = c *: symmetric_tuple_component ([tuple] : 0.-tuple V).
Proof.
apply: val_inj.
change (symmetric_degree 0 (symmetric_scalar V c) =
  c *: component_val (symmetric_tuple_component ([tuple] : 0.-tuple V))).
rewrite symmetric_tuple_componentE symmetric_word_nil.
rewrite /symmetric_scalar linearZ symmetric_unit_homogeneous.
by [].
Qed.

(** Source for [symmetric_degree_zero_pairing]: Federer 1.10.5,
    p. 48, supporting scalar interpretation of the dual mass
    supremum. Pairing a zero-vector with a zero-form multiplies its
    scalar coordinate by the sole value of the form. *)
Lemma symmetric_degree_zero_pairing (K : fieldType) (V W : lmodType K)
    (x : symmetric_power V 0) (f : S_m V W 0) :
  symmetric_pairing x f = symmetric_zeroth_inverse V x *: f [tuple].
Proof.
rewrite -[x](@symmetric_zeroth_inverseK K V x) symmetric_zeroth_tuple_scalar.
rewrite (linZ (proj1 (@symmetric_pairing_bilinear K V W 0) f)) symmetric_pairing_tuple.
by rewrite -symmetric_zeroth_tuple_scalar symmetric_zeroth_inclusionK.
Qed.
