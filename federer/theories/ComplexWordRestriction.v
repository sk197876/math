(** Federer (1969), 1.6.6, p. 27: complex products regarded as real forms.
    This comparison uses the permutation formula of 1.4.2, p. 19, and holds
    without a dimension restriction. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import AlternatingCoordinates OneFormProducts Bilinear AlgebraUP
  ComplexScalarSealed ComplexCharacteristic ComplexCoefficientAlgebra
  ComplexAlternatingForms ScalarRestriction ScalarRestrictionProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Words.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Local Notation hR := (real_two_nonzero R).
Local Notation hC := (complex_two_nonzero R).
Variable V : lmodType C.

(** Source for [restrict_one_forms_wedge]: Federer 1.6.6,
    p. 27, displayed products. The complex and real products agree
    after restriction of the complex factors, also for an empty family. *)
Theorem restrict_one_forms_wedge m (a : 'I_m -> A_m V C^o 1) :
  restrict_form embed (one_forms_wedge hC (scalar_bilinear C) (1:C) a) =
  one_forms_wedge hR (alg_bilinear CR) (1:C) (fun j => restrict_form embed (a j)).
Proof.
apply: form_ext => t.
change (one_forms_wedge hC (scalar_bilinear C) (1:C) a t =
  one_forms_wedge hR (alg_bilinear CR) (1:C) (fun j => restrict_form embed (a j)) t).
rewrite (one_forms_wedge_permutations hC (scalar_bilinear C) (@mulr1 C))
  (one_forms_wedge_permutations hR (alg_bilinear CR) (@alg_unitr R CR)).
apply: eq_bigr => s _.
change (FedererPermutation.index C s * foldr *%R 1
  [seq a j [tuple tnth t (s j)] | j <- enum 'I_m] =
  embed (FedererPermutation.index R s) * foldr *%R 1
  [seq a j [tuple tnth t (s j)] | j <- enum 'I_m]).
by rewrite restriction_permutation_sign.
Qed.
End Words.
