(** Federer (1969), 4.1.6, p. 351: scalar
    multiplication, characteristic restriction and Baire
    forms use the actual pointwise values. These
    definitions retain every point of the original domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals topology.
From Federer Require Import Hom RealNormUP NormMetric BaireFunctions AlternatingForms
  PointwiseFieldSpaceSealed PointwiseFieldMaps DifferentialFormFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_field_times_form]: a scalar
    function multiplies a form pointwise, Federer
    4.1.6, pp. 351–352, including its
    original coefficient expansion. *)
Definition scalar_field_times_form (K:fieldType) (X:choiceType)
    (V W:lmodType K) m (c:X->K) (phi:differential_form_space K X V W m):
    differential_form_space K X V W m:=
  @PointwiseFieldSpace.of_function K X (A_m V W m)
    (fun x=>c x *:@differential_form_value K X V W m phi x).

(** Source for [scalar_field_times_form_values]: the
    original pointwise scalar operation,
    Federer 4.1.6, p. 351. *)
Lemma scalar_field_times_form_values (K:fieldType) (X:choiceType)
    (V W:lmodType K) m (c:X->K) (phi:differential_form_space K X V W m) x:
  @differential_form_value K X V W m (scalar_field_times_form c phi) x=
    c x *:@differential_form_value K X V W m phi x.
Proof. exact:PointwiseFieldSpace.value_of_function. Qed.

(** Source for [characteristic_form_restriction]: E wedge
    phi means multiplication by the characteristic
    function of E, Federer 4.1.6, p. 351. *)
Definition characteristic_form_restriction (K:fieldType) (X:choiceType)
    (V W:lmodType K) m (E:X->Prop) (phi:differential_form_space K X V W m):
    differential_form_space K X V W m:=
  scalar_field_times_form (fun x=>if pselect (E x) then 1 else 0) phi.

(** Source for [characteristic_form_restriction_values]:
    the original E wedge phi agrees with phi on E
    and is zero elsewhere, Federer 4.1.6,
    p. 351, without a measurability assumption. *)
Lemma characteristic_form_restriction_values (K:fieldType) (X:choiceType)
    (V W:lmodType K) m (E:X->Prop) (phi:differential_form_space K X V W m) x:
  @differential_form_value K X V W m (characteristic_form_restriction E phi) x=
    if pselect (E x) then @differential_form_value K X V W m phi x else 0.
Proof. rewrite scalar_field_times_form_values; by case:pselect=>hE; rewrite ?scale1r ?scale0r. Qed.
