(** Federer (1969), 4.1.6, p. 353: the
    original coordinate proof of the graded Leibniz
    identity. Work in the existing full alternating
    algebra to compare the naturally equal degrees
    without replacing the original products or signs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear Alternating AlternatingProduct
  ScalarCoefficients TwoFormBlocks NormBilinearDifferentialAlgebra
  GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateForms
  ScalarTensorContraction MixedAlternatingProduct MixedOrdinaryFormProduct
  ExteriorDifferentialSealed ExteriorDerivativeCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ExteriorDifferentialLeibnizAlgebra.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation fw:=(form_wedge h2 (scalar_bilinear R)).
Local Notation aw:=(alternating_wedge h2 (scalar_bilinear R)).
Local Notation hb:=(@alternating_wedge_bilinear R h2 X R^o _ (scalar_bilinear R)).
Local Notation hA:=(@alternating_wedge_associative R h2 X R^o _ (scalar_bilinear R) (@mulrA R)).

(** Source for [original_one_form_leibniz_step]: commuting
    DX_j past phi gives exactly (-1)^degree(phi),
    the third displayed calculation in Federer
    4.1.6, p. 353. *)
Lemma original_one_form_leibniz_step p q (a:A_m X R^o 1)
    (phi dphi:A_m X R^o p) (psi dpsi:A_m X R^o q):
  form_include (fw a (fw dphi psi+fw phi dpsi))=
    aw (form_include (fw a dphi)) (form_include psi)+
      (-1:R)^+p*:aw (form_include phi) (form_include (fw a dpsi)).
Proof.
rewrite !form_wedge_include.
have hAdd:form_include (fw dphi psi+fw phi dpsi)=
    form_include (fw dphi psi)+form_include (fw phi dpsi):=linearD _ _ _.
rewrite hAdd !form_wedge_include (bilDr hb) !hA.
have hComm:aw (form_include a) (form_include phi)=
    (-1:R)^+p*:aw (form_include phi) (form_include a).
  have h:=@alternating_wedge_anticommutative R h2 X R^o _ (scalar_bilinear R)
    (@mulrC R) 1 p (form_include a) (form_include phi)
    (form_include_homogeneous a) (form_include_homogeneous phi).
  by rewrite mul1n in h.
rewrite hComm (bilZl hb).
by rewrite -hA.
Qed.

(** Source for [exterior_differential_product_linearization]:
    applying exterior alternation to the actual
    product differential yields the two original
    graded terms, Federer 4.1.6, p. 353.
    Inclusion in the original full alternating algebra
    only identifies the equal result degrees. *)
Theorem exterior_differential_product_linearization p q
    (phi:A_m X R^o p) (psi:A_m X R^o q)
    (L:Hom X (A_m X R^o p)) (M:Hom X (A_m X R^o q)):
  form_include (@ExteriorDifferential.value R h2 n R^o (p+q)
    (norm_bilinear_product_linear_term (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) p q)
      phi psi L M))=
    aw (form_include (@ExteriorDifferential.value R h2 n R^o p L)) (form_include psi)+
      (-1:R)^+p*:aw (form_include phi) (form_include (@ExteriorDifferential.value R h2 n R^o q M)).
Proof.
rewrite !exterior_differential_coordinate_formula.
rewrite !linear_sum.
rewrite (big_morph (fun a=>aw a (form_include psi)) (fun a b=>bilDl hb a b (form_include psi)) (bil0l hb (form_include psi)))
  (big_morph (aw (form_include phi)) (bilDr hb _) (bil0r hb _)) scaler_sumr -big_split.
apply:eq_bigr=>j _.
change (form_include (mixed_form_product h2 (@scalar_action_bilinear R R^o)
  (euclidean_coordinate_form j)
  (fw (L (@coordinate_basis R n j)) psi+fw phi (M (@coordinate_basis R n j))))=
  aw (form_include (mixed_form_product h2 (@scalar_action_bilinear R R^o)
    (euclidean_coordinate_form j) (L (@coordinate_basis R n j)))) (form_include psi)+
    (-1:R)^+p*:aw (form_include phi)
      (form_include (mixed_form_product h2 (@scalar_action_bilinear R R^o)
        (euclidean_coordinate_form j) (M (@coordinate_basis R n j))))).
rewrite !mixed_real_form_product.
exact:original_one_form_leibniz_step.
Qed.
End ExteriorDifferentialLeibnizAlgebra.
