(** Federer (1969), 1.8.2, p. 40: applying the alternating two-form normal
    form of 1.7.3, pp. 29-30, while retaining the orthonormal vector pairs
    as well as their polarity covectors. Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerPolarity InnerDual LinearBasis
  BilinearRepresentation TwoFormBilinear SymmetricEndomorphisms
  SkewNormalFormUP SkewNormalFormSealed OrthonormalFamilies
  AlternatingForms AlternatingProduct ScalarCoefficients TwoCovectorProduct
  FormEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [alternating_two_form_vector_normal_form]: Federer
    1.8.2, p. 40, choose orthonormal vector pairs and the dual
    one-covectors with nonnegative coefficients for the pulled-back
    two-form. The family here may omit zero blocks; later dimension
    and vanishing results handle that case explicitly. *)
Theorem alternating_two_form_vector_normal_form (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (phi : A_m V R^o 2) :
  exists m (a b : 'I_m -> V) (lambda : 'I_m -> R),
    orthonormal_family B (paired_family a b) /\
    (forall i, 0 <= lambda i) /\
    phi = \sum_i lambda i *: form_wedge h2 (scalar_bilinear R) (inner_polarity hB (a i)) (inner_polarity hB (b i)).
Proof.
have [f hf] := @bilinear_endomorphism_representation R V B
  (fun x y => phi [tuple x; y]) hB (two_form_bilinear phi) n e he.
have hs : is_skewsymmetric_endomorphism B f.
  move=> x y; rewrite (inner_symmetric hB x (f y)) !hf.
  exact: two_form_skew.
have [m [a [b [lambda [ho [hl hform]]]]]] :=
  @SkewNormalForm.exists_blocks R V B hB n e he f hs.
pose alpha := fun i => inner_polarity hB (a i).
pose beta := fun i => inner_polarity hB (b i).
exists m, a, b, lambda; split=> //; split=> //.
  apply: form_ext => /tupleP [x t]; case/tupleP: t => y t; rewrite (tuple0 t).
  change (phi [tuple x; y] = form_evaluate [tuple x; y]
    (\sum_i lambda i *: form_wedge h2 (scalar_bilinear R) (alpha i) (beta i))).
  rewrite linear_sum.
  under eq_bigr do rewrite linearZ.
  change (phi [tuple x; y] = \sum_i lambda i *
    (form_wedge h2 (scalar_bilinear R) (alpha i) (beta i) [tuple x; y])).
  under eq_bigr do rewrite inner_covector_pair_product.
  by rewrite -hf hform.
Qed.
