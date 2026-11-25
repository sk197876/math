(** Federer (1969), 4.1.6, p. 353: the two
    successive scalar one-covector operations have
    opposite signs. Reuse the original coassociative
    contraction and graded commutation of Chapter 1;
    arbitrary vector coefficients are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Bilinear BilinearNegation Exterior Alternating
  ScalarCoefficients FormEvaluation ScalarTensorContraction LeftInteriorHom Convolution
  ConvolutionCommutativity DualExterior MixedTensorPairing MixedHomogeneousConvolution
  MixedAlternatingProduct MixedScalarContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [mixed_scalar_product_homogeneous]: the
    original product/contraction diagram at every
    exterior vector, supporting Federer
    4.1.6, p. 353. *)
Lemma mixed_scalar_product_homogeneous (K:fieldType) (h2:(1+1:K)!=0)
    (V W:lmodType K) p q (a:A_m V K^o p) (b:A_m V W q) (z:exterior_space V):
  form_homogeneous (mixed_form_product h2 (@scalar_action_bilinear K W) a b) z=
    form_homogeneous b (left_interior_hom h2 z (form_homogeneous a)).
Proof.
rewrite /mixed_form_product homogeneous_formK mixed_homogeneous_convolutionE.
exact:esym (mixed_scalar_contract_pairing _ _ _).
Qed.

(** Source for [scalar_covector_contraction_skew]: the
    original two coordinate one-covectors anticommute,
    used to cancel the double derivative in
    Federer 4.1.6, p. 353. *)
Lemma scalar_covector_contraction_skew (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) (a b:A_m V K^o 1) (z:exterior_space V):
  left_interior_hom h2 (left_interior_hom h2 z (form_homogeneous a)) (form_homogeneous b)=
    -left_interior_hom h2 (left_interior_hom h2 z (form_homogeneous b)) (form_homogeneous a).
Proof.
have hAB:convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous a) (form_homogeneous b)=
    -convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous b) (form_homogeneous a).
  apply:hom_ext=>x.
  change (convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous a) (form_homogeneous b) x=
    -convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous b) (form_homogeneous a) x).
  have h:=@convolution_anticommutative K (exterior_space V) K^o (exterior_grading V)
    (fun x y:K^o=>x*y) (scalar_bilinear K) (@mulrC K) 1 1
    (form_homogeneous a) (form_homogeneous b) (Psi h2 V) (@Psi_anticommutative K h2 V) x.
  by rewrite muln1 expr1 scaleN1r in h.
rewrite -!left_interior_hom_associative hAB.
exact:(bilNr (@left_interior_hom_bilinear K h2 V) z _).
Qed.

(** Source for [mixed_scalar_one_products_skew]:
    DX_k wedge DX_j wedge eta is minus its
    exchanged product, Federer 4.1.6,
    p. 353, for every vector coefficient eta. *)
Theorem mixed_scalar_one_products_skew (K:fieldType) (h2:(1+1:K)!=0)
    (V W:lmodType K) m (a b:A_m V K^o 1) (c:A_m V W m):
  mixed_form_product h2 (@scalar_action_bilinear K W) a
    (mixed_form_product h2 (@scalar_action_bilinear K W) b c)=
  -mixed_form_product h2 (@scalar_action_bilinear K W) b
    (mixed_form_product h2 (@scalar_action_bilinear K W) a c).
Proof.
apply:form_ext=>t.
change (form_evaluate t (mixed_form_product h2 (@scalar_action_bilinear K W) a
    (mixed_form_product h2 (@scalar_action_bilinear K W) b c))=
  form_evaluate t (-mixed_form_product h2 (@scalar_action_bilinear K W) b
    (mixed_form_product h2 (@scalar_action_bilinear K W) a c))).
rewrite linearN /form_evaluate.
change (mixed_form_product h2 (@scalar_action_bilinear K W) a
    (mixed_form_product h2 (@scalar_action_bilinear K W) b c) t=
  -mixed_form_product h2 (@scalar_action_bilinear K W) b
    (mixed_form_product h2 (@scalar_action_bilinear K W) a c) t).
rewrite !mixed_scalar_form_product_contraction !mixed_scalar_product_homogeneous.
by rewrite scalar_covector_contraction_skew linearN.
Qed.
