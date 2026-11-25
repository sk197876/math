(** Federer (1969), 4.1.6, pp. 352–353: existence
    of the independently specified exterior-differential
    value, with its original coordinate formula.
    The coordinate sum is only an existence witness;
    consumers use the sealed characteristic laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear Alternating FormEvaluation OneFormLinear OneFormIdentification
  ScalarTensorContraction GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateTopology
  EuclideanScalarCoordinateMaps EuclideanCoordinateForms ExteriorDifferentialUP
  ExteriorDifferentialNormBound MixedAlternatingProduct ScalarOneFormProductOmission.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_differential_witness]:
    sum_j X_j wedge L(e_j), the coordinate formula
    from Federer 4.1.6, p. 353. It proves
    existence of the original signed value. *)
Definition euclidean_exterior_differential_witness (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) m (L:Hom (R_n R n) (A_m (R_n R n) W m)):
    A_m (R_n R n) W m.+1:=
  \sum_(j:'I_n) mixed_form_product h2 (@scalar_action_bilinear R W)
    (euclidean_coordinate_form j) (L (@coordinate_basis R n j)).

(** Source for [euclidean_exterior_differential_witness_laws]:
    the coordinate formula has every original signed
    tuple evaluation, Federer 4.1.6,
    pp. 352–353, including n=0 and m=0. *)
Lemma euclidean_exterior_differential_witness_laws (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) m (L:Hom (R_n R n) (A_m (R_n R n) W m)):
  is_exterior_differential_value L (euclidean_exterior_differential_witness h2 L).
Proof.
move=>t; rewrite /euclidean_exterior_differential_witness exterior_differential_trace_tuple_values.
change (form_evaluate t (\sum_(j:'I_n) mixed_form_product h2
  (@scalar_action_bilinear R W) (euclidean_coordinate_form j) (L (@coordinate_basis R n j)))=
  \sum_(i:'I_m.+1) (-1:R)^+(val i)*:(L (tnth t i)) (exterior_omitted_tuple t i)).
rewrite linear_sum /form_evaluate.
change ((\sum_(j:'I_n) mixed_form_product h2
  (@scalar_action_bilinear R W) (euclidean_coordinate_form j)
    (L (@coordinate_basis R n j)) t)=
  \sum_(i:'I_m.+1) (-1:R)^+(val i)*:(L (tnth t i)) (exterior_omitted_tuple t i)).
have hProduct j:
  mixed_form_product h2 (@scalar_action_bilinear R W)
    (euclidean_coordinate_form j) (L (@coordinate_basis R n j)) t=
    \sum_(i:'I_m.+1) (-1:R)^+(val i)*:
      (one_hom (euclidean_coordinate_form j) (tnth t i)*:
        L (@coordinate_basis R n j) (exterior_omitted_tuple t i)).
  exact:scalar_one_form_product_omission.
under [LHS]eq_bigr do rewrite hProduct.
rewrite exchange_big.
apply:eq_bigr=>i _.
have hCoordinate j:one_hom (euclidean_coordinate_form j) (tnth t i)=(tnth t i) j.
  by rewrite /euclidean_coordinate_form one_formK.
have hExpansion:L (tnth t i)=\sum_(j:'I_n) (tnth t i) j *:L (@coordinate_basis R n j).
  rewrite -{1}(euclidean_coordinate_expansion (tnth t i)) linear_sum.
  by apply:eq_bigr=>j _; rewrite linearZ.
rewrite hExpansion.
change ((\sum_(j:'I_n) (-1:R)^+(val i)*:
  (one_hom (euclidean_coordinate_form j) (tnth t i)*:
    L (@coordinate_basis R n j) (exterior_omitted_tuple t i)))=
  (-1:R)^+(val i)*:form_evaluate (exterior_omitted_tuple t i)
    (\sum_(j:'I_n) (tnth t i) j*:L (@coordinate_basis R n j))).
rewrite linear_sum /form_evaluate scaler_sumr.
apply:eq_bigr=>j _; by rewrite hCoordinate.
Qed.

(** Source for [euclidean_exterior_differential_exists]:
    the signed formula defines an alternating form,
    Federer 4.1.6, p. 352. Arbitrary vector
    coefficients and every exterior degree are retained. *)
Theorem euclidean_exterior_differential_exists (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) m (L:Hom (R_n R n) (A_m (R_n R n) W m)):
  exists a:A_m (R_n R n) W m.+1,is_exterior_differential_value L a.
Proof. exists (euclidean_exterior_differential_witness h2 L); exact:euclidean_exterior_differential_witness_laws. Qed.
