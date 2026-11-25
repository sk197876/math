(** Federer (1969), 4.1.6, p. 351: the vector spaces
    of differential forms and multivector fields on the
    original domain. Their carriers are opaque; evaluation
    identifies them with exactly the original functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP ExteriorGrading AlternatingForms AlternatingProduct
  PointwiseFieldSpaceUP PointwiseFieldSpaceSealed PointwiseFieldMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [differential_form_space]: maps of the
    original domain into A^m(V,W), Federer 4.1.6,
    p. 351, using V=R^n for the printed forms. *)
Definition differential_form_space (K:fieldType) (X:choiceType)
    (V W:lmodType K) m:lmodType K:=
  @PointwiseFieldSpace.space K X (A_m V W m).
Arguments differential_form_space K X V W m : clear implicits.

(** Source for [differential_form_value]: the actual
    value phi(x) of an original form,
    Federer 4.1.6, p. 351. *)
Definition differential_form_value (K:fieldType) (X:choiceType)
    (V W:lmodType K) m:
    Hom (differential_form_space K X V W m)
      (GRing.Lmodule.clone K (X->A_m V W m) _):=
  @PointwiseFieldSpace.value K X (A_m V W m).

(** Source for [differential_form_space_laws]: exact
    pointwise representation and vector operations,
    Federer 4.1.6, p. 351. *)
Theorem differential_form_space_laws (K:fieldType) (X:choiceType)
    (V W:lmodType K) m:
  is_pointwise_field_space (@differential_form_value K X V W m).
Proof. exact:PointwiseFieldSpace.laws. Qed.

(** Source for [multivector_field_space]: maps into
    Lambda_m V, Federer 4.1.6, p. 351. *)
Definition multivector_field_space (K:fieldType) (X:choiceType) (V:lmodType K) m:lmodType K:=
  @PointwiseFieldSpace.space K X (exterior_power V m).
Arguments multivector_field_space K X V m : clear implicits.

(** Source for [multivector_field_value]: the actual
    value xi(x), Federer 4.1.6, p. 351. *)
Definition multivector_field_value (K:fieldType) (X:choiceType) (V:lmodType K) m:
    Hom (multivector_field_space K X V m)
      (GRing.Lmodule.clone K (X->exterior_power V m) _):=
  @PointwiseFieldSpace.value K X (exterior_power V m).

(** Source for [multivector_field_space_laws]: the
    original vector fields have exact pointwise
    representation, Federer 4.1.6, p. 351. *)
Theorem multivector_field_space_laws (K:fieldType) (X:choiceType) (V:lmodType K) m:
  is_pointwise_field_space (@multivector_field_value K X V m).
Proof. exact:PointwiseFieldSpace.laws. Qed.

(** Source for [differential_form_product]: the displayed
    pointwise alternating product, Federer 4.1.6,
    p. 351, for any bilinear coefficient multiplication. *)
Definition differential_form_product (K:fieldType) (h2:(1+1:K)!=0)
    (X:choiceType) (V W:lmodType K) (mu:W->W->W) (hmu:bilinear mu) p q:
    differential_form_space K X V W p->differential_form_space K X V W q->
      differential_form_space K X V W (p+q):=
  @pointwise_field_binary K X (A_m V W p) (A_m V W q) (A_m V W (p+q))
    (@form_wedge K h2 V W mu hmu p q).

(** Source for [differential_form_product_values]: the
    first displayed equation in Federer 4.1.6,
    p. 351, holds on every original domain point. *)
Lemma differential_form_product_values (K:fieldType) (h2:(1+1:K)!=0)
    (X:choiceType) (V W:lmodType K) (mu:W->W->W) (hmu:bilinear mu) p q
    (phi:differential_form_space K X V W p) (psi:differential_form_space K X V W q) x:
  @differential_form_value K X V W (p+q) (differential_form_product h2 hmu phi psi) x=
    form_wedge h2 hmu (@differential_form_value K X V W p phi x)
      (@differential_form_value K X V W q psi x).
Proof. exact:pointwise_field_binary_values. Qed.

(** Source for [differential_form_product_bilinear]: the
    alternating product of fields retains the coefficient
    algebra bilinearity, Federer 4.1.6, p. 351. *)
Lemma differential_form_product_bilinear (K:fieldType) (h2:(1+1:K)!=0)
    (X:choiceType) (V W:lmodType K) (mu:W->W->W) (hmu:bilinear mu) p q:
  bilinear (@differential_form_product K h2 X V W mu hmu p q).
Proof.
exact:(@pointwise_field_binary_bilinear K X (A_m V W p) (A_m V W q) (A_m V W (p+q))
  (@form_wedge K h2 V W mu hmu p q) (@form_wedge_bilinear K h2 V W mu hmu p q)).
Qed.
