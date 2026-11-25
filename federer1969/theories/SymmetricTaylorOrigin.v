(** Federer (1969), 3.4.5, p. 319: recover
    the prescribed coefficient of each homogeneous Taylor term
    in the analytic-realisation argument, using 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom Bilinear Graded HomogeneousHom SymmetricAlgebra SymmetricGrading SymmetricForms
  SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism SymmetricDividedMonomials
  PolynomialTaylorTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Origin.
Variable K:fieldType.
Variables X Y:lmodType K.

(** Source for [symmetric_taylor_origin_same_degree]: the
    m-th differential coefficient at zero of the original
    homogeneous term equals its defining m-form, 1.10.4,
    p. 46, as used in 3.4.5, p. 319. *)
Lemma symmetric_taylor_origin_same_degree m (phi:S_m X Y m):
  symmetric_taylor_term m phi 0=phi.
Proof.
apply:sform_ext=>t.
rewrite -!sform_wordsE -!sform_extensionE.
change (sform_homogeneous (symmetric_taylor_term m phi 0) (symmetric_word t)=
  sform_homogeneous phi (symmetric_word t)).
have hDegree:homogeneous (symmetric_grading X) m (symmetric_word t).
  have hh:=symmetric_word_homogeneous t;by rewrite size_tuple in hh.
rewrite (symmetric_taylor_term_pairing _ _ hDegree) subnn.
by rewrite /symmetric_divided_vector_power fact0 invr1 scale1r
  /symmetric_vector_power /= symmetric_word_nil symmetric_product_unitr.
Qed.

(** Source for [symmetric_taylor_origin_lower_degree]: every
    lower derivative of a positive-degree homogeneous term
    vanishes at zero, 1.10.4, p. 46, supporting
    coefficient recovery in 3.4.5, p. 319. *)
Lemma symmetric_taylor_origin_lower_degree m i (phi:S_m X Y m):
  (i<m)%N ->symmetric_taylor_term i phi 0=0.
Proof.
move=>hIM;apply:sform_ext=>t;rewrite sform_zeroE.
rewrite -sform_wordsE -(sform_extensionE _).
change (sform_homogeneous (symmetric_taylor_term i phi 0) (symmetric_word t)=0).
have hDegree:homogeneous (symmetric_grading X) i (symmetric_word t).
  have hh:=symmetric_word_homogeneous t;by rewrite size_tuple in hh.
rewrite (symmetric_taylor_term_pairing _ _ hDegree).
have hNe:(m-i)%N!=0 by rewrite -lt0n subn_gt0.
have hPower:symmetric_divided_vector_power (0:X) (m-i)=0.
  rewrite /symmetric_divided_vector_power -{1}[0:X](scale0r (0:X))
    symmetric_vector_power_scale expr0n (negbTE hNe) scale0r scaler0.
  reflexivity.
by rewrite hPower (bil0r (@symmetric_product_bilinear K X)) linear0.
Qed.
End Origin.
