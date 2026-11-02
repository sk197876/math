(** Federer (1969), 1.6.6, p. 27: mixed products of complex one-forms. This
    supporting comparison transports products through the proved
    complex-coordinate extension. Source context are recorded in
    ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import AlternatingCoordinates OneFormProducts Bilinear AlgebraUP
  ComplexScalarSealed ComplexCoefficientAlgebra ComplexValuedForms
  ComplexAlternatingForms ComplexCoordinateRestriction ScalarRestrictionProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Words.
Variable R : realFieldType.
Hypothesis hR : (1+1 : R) != 0.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation CR := (complex_real_algebra R).
Variable U : lmodType R.

(** Source for [complex_values_word]: Federer 1.6.6, p. 27,
    products of one-forms. The ordered product, interpreted as a
    complex-valued real alternating form, including the empty product. *)
Definition complex_values_word m (a : 'I_m -> complex_valued_form embed U C^o 1) :=
  real_as_complex_valued (one_forms_wedge hR (alg_bilinear CR) (1:C)
    (fun j => complex_valued_as_real (a j))).

Variable n : nat.
Variable e : 'I_n -> U.
Hypothesis he : is_basis e.
Hypothesis hC : (1+1 : C) != 0.
Local Notation E := (coordinate_space C n).

(** Source for [coordinate_restriction_singleton]: Federer
    1.6.6, p. 27, mixed basis. Supporting evaluation of a restricted
    one-form on a single vector. *)
Lemma coordinate_restriction_singleton (a : A_m E C^o 1) v :
  coordinate_form_restriction embed he a [tuple v] = a [tuple extended_coordinates embed he v].
Proof. by rewrite coordinate_form_restrictionE; congr (a _); apply: val_inj. Qed.

(** Source for [coordinate_restriction_word]: Federer 1.6.6,
    p. 27, mixed basis. The complex coordinate comparison preserves
    every ordered alternating product of one-forms. *)
Theorem coordinate_restriction_word m (a : 'I_m -> A_m E C^o 1) :
  coordinate_form_restriction embed he (one_forms_wedge hC (scalar_bilinear C) (1:C) a) =
  complex_values_word (fun j => coordinate_form_restriction embed he (a j)).
Proof.
apply: complex_valued_form_ext => t.
rewrite coordinate_form_restrictionE.
change (one_forms_wedge hC (scalar_bilinear C) (1:C) a (map_tuple (extended_coordinates embed he) t) =
  one_forms_wedge hR (alg_bilinear CR) (1:C)
    (fun j => complex_valued_as_real (coordinate_form_restriction embed he (a j))) t).
rewrite (one_forms_wedge_permutations hC (scalar_bilinear C) (@mulr1 C))
  (one_forms_wedge_permutations hR (alg_bilinear CR) (@alg_unitr R CR)).
apply: eq_bigr => s _.
change (FedererPermutation.index C s *
  foldr *%R 1 [seq a j [tuple tnth (map_tuple (extended_coordinates embed he) t) (s j)] | j <- enum 'I_m] =
  embed (FedererPermutation.index R s) *
  foldr *%R 1 [seq coordinate_form_restriction embed he (a j) [tuple tnth t (s j)] | j <- enum 'I_m]).
rewrite restriction_permutation_sign; congr (_ * _); congr (foldr _ _ _).
apply: eq_map => j; by rewrite coordinate_restriction_singleton tnth_map.
Qed.
End Words.
