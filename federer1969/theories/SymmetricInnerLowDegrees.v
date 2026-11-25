(** Federer (1969), 1.10.5, p. 47: the induced inner product retains the
    scalar and vector inner products in degrees zero and one. The proof uses
    the previously proved permutation formula. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Bilinear GradedComponents SymmetricAlgebra SymmetricGrading
  SymmetricLowPowers SymmetricFormIsomorphism SymmetricDegreeZeroPairing
  InnerProductUP InnerNorm InnerSymmetric InnerSymmetricPositivity
  SymmetricInnerNorm SymmetricInnerPurePowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_first_tuple]: Federer 1.10.5,
    p. 47, supporting degree-one identification: inclusion of
    a vector is its one-factor symmetric product. *)
Lemma symmetric_first_tuple (K : fieldType) (V : lmodType K) x :
  symmetric_first_inclusion V x = symmetric_tuple_component [tuple x].
Proof.
apply: val_inj.
change (symmetric_degree 1 (symmetric_generator x) = component_val (symmetric_tuple_component [tuple x])).
by rewrite symmetric_generator_homogeneous symmetric_tuple_componentE /=
  symmetric_word_cons symmetric_word_nil symmetric_product_unitr.
Qed.

(** Source for [symmetric_inner_first_agreement]: Federer 1.10.5, p. 47,
    induced inner products The degree-one inner product is the original one. *)
Lemma symmetric_inner_first_agreement (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) x y :
  symmetric_inner_form hB (symmetric_first_inclusion V x) (symmetric_first_inclusion V y) = B x y.
Proof.
rewrite !symmetric_first_tuple.
have hh := @symmetric_inner_pure_powers R V B hB 1 x y.
have tx : [tuple x | i<1] = [tuple x] by apply: eq_from_tnth=> i; rewrite ord1 tnth_mktuple tnth0.
have ty : [tuple y | i<1] = [tuple y] by apply: eq_from_tnth=> i; rewrite ord1 tnth_mktuple tnth0.
by rewrite tx ty factS fact0 muln1 mul1r expr1 in hh.
Qed.

(** Source for [symmetric_inner_zeroth_agreement]: Federer 1.10.5, p. 47,
    induced inner products The degree-zero inner product is scalar
    multiplication. *)
Lemma symmetric_inner_zeroth_agreement (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a b : R) :
  symmetric_inner_form hB (symmetric_zeroth_inclusion V a) (symmetric_zeroth_inclusion V b) = a*b.
Proof.
rewrite !symmetric_zeroth_tuple_scalar
  (bilZl (symmetric_inner_form_bilinear hB 0)) (bilZr (symmetric_inner_form_bilinear hB 0)).
have hh := @symmetric_inner_pure_powers R V B hB 0 (0:V) (0:V).
rewrite !tuple0 fact0 expr0 mulr1 in hh.
change (a * (b * symmetric_inner_form hB
  (symmetric_tuple_component ([tuple] : 0.-tuple V))
  (symmetric_tuple_component ([tuple] : 0.-tuple V))) = a*b).
by rewrite hh mulr1.
Qed.

(** Source for [symmetric_inner_norm_first_agreement]: Federer
    1.10.5, p. 47, supporting agreement of the induced
    norm with the original vector norm in degree one. *)
Lemma symmetric_inner_norm_first_agreement (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) x :
  symmetric_inner_norm hB (symmetric_first_inclusion V x) = inner_norm hB x.
Proof.
apply: inner_norm_value; first exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr symmetric_inner_first_agreement.
Qed.

(** Source for [symmetric_inner_norm_zeroth_agreement]: Federer
    1.10.5, p. 47, supporting agreement of the induced
    norm with absolute value on scalars in degree zero. *)
Lemma symmetric_inner_norm_zeroth_agreement (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : R) :
  symmetric_inner_norm hB (symmetric_zeroth_inclusion V a) = `|a|.
Proof.
apply: inner_norm_value; first exact: normr_ge0.
by rewrite -normrX (ger0_norm (sqr_ge0 a)) symmetric_inner_zeroth_agreement expr2.
Qed.
