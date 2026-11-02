(** Federer (1969), 1.6.5, p. 25, the change-of-dual-bases
    observation. Supporting basis expansion of any top form and
    transfer of the contraction identity under scaling the volume.
    In the printed identity the upper and lower dualities reduce
    to one linear dependence on the volume, as shown on p. 26. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleAdaptedBasis
  CovectorProductNaturality ProductContractionAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [top_form_rebased]: Federer 1.6.5, p. 25,
    change-of-dual-bases observation. Supporting fact: any top-form
    functional is a scalar multiple of the dual volume of any
    basis of the same dimension. The scalar may be zero. *)
Lemma top_form_rebased (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) N (b : 'I_N -> V) (hb : is_basis b)
  n (phi : A_m V K^o n) : n = N -> exists c : K,
    (form_homogeneous phi : Hom (exterior_space V) K^o) =
      c *: (form_homogeneous
        (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o)
          (fun i => one_form (dual_basis hb i))) : Hom (exterior_space V) K^o).
Proof.
move=> hn; subst n.
exists (pairing (e_lambda b (val (Lambda_top N))) phi : K).
have h := top_covector_expansion h2 hb phi.
apply: hom_ext => x.
rewrite {1}h linearZ hom_m_scaleE hom_scaleE omega_lambda_top_product.
by [].
Qed.

(** Source for [product_identity_volume_scale]: Federer 1.6.5,
    p. 25, multiplying both members under a change of volume.
    Supporting transfer of the full-algebra identity under arbitrary
    scalar multiplication of the volume functional. *)
Lemma product_identity_volume_scale (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) (a : Hom (exterior_space V) K^o) x y c s :
  product_contraction_hom h2 a x y = s *: diagonal_contraction_hom h2 a x y ->
  product_contraction_hom h2 (c *: a) x y = s *: diagonal_contraction_hom h2 (c *: a) x y.
Proof.
move=> h; rewrite (linZ (product_contraction_volume_linear h2 x y))
  (linZ (diagonal_contraction_volume_linear h2 x y)) h !scalerA.
by rewrite mulrC.
Qed.

(** Source for [product_identity_input_scales]: Federer 1.6.5,
    pp. 25-26, supporting extension from reordered basis products.
    Independent scalar factors on the two input words multiply
    both members by their product. *)
Lemma product_identity_input_scales (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) (a : Hom (exterior_space V) K^o) x y c d s :
  product_contraction_hom h2 a x y = s *: diagonal_contraction_hom h2 a x y ->
  product_contraction_hom h2 a (c *: x) (d *: y) =
    s *: diagonal_contraction_hom h2 a (c *: x) (d *: y).
Proof.
move=> h; rewrite (bilZl (product_contraction_hom_bilinear h2 a))
  (bilZr (product_contraction_hom_bilinear h2 a))
  (bilZl (diagonal_contraction_hom_bilinear h2 a))
  (bilZr (diagonal_contraction_hom_bilinear h2 a)) h !scalerA.
congr (_ *: _); by rewrite -!mulrA [d*s]mulrC !mulrA [c*s]mulrC.
Qed.
