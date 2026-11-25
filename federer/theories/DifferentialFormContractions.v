(** Federer (1969), 4.1.6, p. 351: both original
    interior operations and the equal-degree pairing act
    pointwise on forms and multivector fields. The actual
    Chapter 1 operations supply all fibre values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP ExteriorGrading AlternatingForms AlternatingPairing
  InteriorMultiplication PointwiseFieldSpaceUP PointwiseFieldSpaceSealed PointwiseFieldMaps DifferentialFormFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [field_right_interior]: xi right-contracted
    into a form, Federer 4.1.6, p. 351,
    with the original p<=q degree condition. *)
Definition field_right_interior (K:fieldType) (X:choiceType) (V W:lmodType K)
    p q (hpq:(p<=q)%N):
    multivector_field_space K X V p->differential_form_space K X V W q->
      differential_form_space K X V W (q-p):=
  @pointwise_field_binary K X (exterior_power V p) (A_m V W q) (A_m V W (q-p))
    (@right_interior K V W p q hpq).

(** Source for [field_right_interior_values]: the printed
    pointwise contraction equation, Federer 4.1.6,
    p. 351. *)
Lemma field_right_interior_values (K:fieldType) (X:choiceType) (V W:lmodType K)
    p q (hpq:(p<=q)%N) (xi:multivector_field_space K X V p)
    (phi:differential_form_space K X V W q) x:
  @differential_form_value K X V W (q-p) (field_right_interior hpq xi phi) x=
    right_interior hpq (@multivector_field_value K X V p xi x)
      (@differential_form_value K X V W q phi x).
Proof. exact:pointwise_field_binary_values. Qed.

(** Source for [field_left_interior]: the original
    contraction of a covector field into a multivector
    field, Federer 4.1.6, p. 351. *)
Definition field_left_interior (K:fieldType) (h2:(1+1:K)!=0) (X:choiceType) (V:lmodType K)
    p q (hpq:(p<=q)%N):
    multivector_field_space K X V q->differential_form_space K X V K^o p->
      multivector_field_space K X V (q-p):=
  @pointwise_field_binary K X (exterior_power V q) (A_m V K^o p) (exterior_power V (q-p))
    (@left_interior K h2 V p q hpq).

(** Source for [field_left_interior_values]: the original
    pointwise left-interior definition in Federer
    4.1.6, p. 351. *)
Lemma field_left_interior_values (K:fieldType) (h2:(1+1:K)!=0) (X:choiceType) (V:lmodType K)
    p q (hpq:(p<=q)%N) (xi:multivector_field_space K X V q)
    (phi:differential_form_space K X V K^o p) x:
  @multivector_field_value K X V (q-p) (field_left_interior h2 hpq xi phi) x=
    left_interior h2 hpq (@multivector_field_value K X V q xi x)
      (@differential_form_value K X V K^o p phi x).
Proof. exact:pointwise_field_binary_values. Qed.

(** Source for [field_form_pairing]: the equal-degree
    notation <xi,phi>, Federer 4.1.6, p. 351,
    is pointwise original exterior evaluation. *)
Definition field_form_pairing (K:fieldType) (X:choiceType) (V W:lmodType K) m:
    multivector_field_space K X V m->differential_form_space K X V W m->
      @PointwiseFieldSpace.space K X W:=
  @pointwise_field_binary K X (exterior_power V m) (A_m V W m) W (@pairing K V W m).

(** Source for [field_form_pairing_values]: the actual
    original pairing at each domain point, Federer
    4.1.6, p. 351. *)
Lemma field_form_pairing_values (K:fieldType) (X:choiceType) (V W:lmodType K) m
    (xi:multivector_field_space K X V m) (phi:differential_form_space K X V W m) x:
  @PointwiseFieldSpace.value K X W (field_form_pairing xi phi) x=
    pairing (@multivector_field_value K X V m xi x) (@differential_form_value K X V W m phi x).
Proof. exact:pointwise_field_binary_values. Qed.
