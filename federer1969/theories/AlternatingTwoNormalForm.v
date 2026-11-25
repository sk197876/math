(** Federer (1969), 1.7.3, pp. 29-30: the complete normal form of
    alternating two-forms. Paired indexing (i,false),(i,true) denotes
    consecutive entries 2i+1,2i+2 in the book's orthonormal sequence. *)
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

(** Source for [alternating_two_form_normal_form]: Federer
    1.7.3, pp. 29-30, displayed corollary: an alternating two-form
    is a finite sum of nonnegative multiples of wedge products of
    consecutive members of an orthonormal sequence of one-covectors.
    The empty sum covers the zero form, including dimension zero. *)
Theorem alternating_two_form_normal_form (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (phi : A_m V R^o 2) :
  exists m (alpha beta : 'I_m -> A_m V R^o 1) (lambda : 'I_m -> R),
    orthonormal_family (inner_dual_product hB he) (paired_family alpha beta) /\
    (forall i, 0 <= lambda i) /\
    phi = \sum_i lambda i *: form_wedge h2 (scalar_bilinear R) (alpha i) (beta i).
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
exists m, alpha, beta, lambda; split.
- have hp p : paired_family alpha beta p = inner_polarity hB (paired_family a b p).
    by case: p => [i []].
  by move=> p q; rewrite !hp inner_dual_polarityE ho.
- split; first exact hl.
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
