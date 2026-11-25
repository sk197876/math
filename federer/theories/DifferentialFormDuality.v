(** Federer (1969), 4.1.6, p. 352: original duality
    and Hodge maps on fields are the pointwise maps
    of 1.5.2 and 1.7.8. Their top vector and covector
    are parameters, specialized to the standard coordinate
    volume elements in Euclidean applications. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom ExteriorGrading AlternatingForms DualityMaps HodgeMaps InnerProductUP
  PointwiseFieldSpaceUP PointwiseFieldSpaceSealed PointwiseFieldMaps DifferentialFormFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [field_duality_lower]: D_p xi is
    contraction with the original top covector,
    Federer 4.1.6, p. 352. *)
Definition field_duality_lower (K:fieldType) (X:choiceType) (V:lmodType K)
    n (omega:A_m V K^o n) p (hp:(p<=n)%N):
    multivector_field_space K X V p->differential_form_space K X V K^o (n-p):=
  @pointwise_field_map K X (exterior_power V p) (A_m V K^o (n-p)) (@D_p K V n omega p hp).

(** Source for [field_duality_lower_values]: pointwise
    D_p, Federer 4.1.6, p. 352. *)
Lemma field_duality_lower_values (K:fieldType) (X:choiceType) (V:lmodType K)
    n (omega:A_m V K^o n) p (hp:(p<=n)%N) (xi:multivector_field_space K X V p) x:
  @differential_form_value K X V K^o (n-p) (field_duality_lower omega hp xi) x=
    D_p omega hp (@multivector_field_value K X V p xi x).
Proof. exact:pointwise_field_map_values. Qed.

(** Source for [field_duality_upper]: D^p phi is
    contraction into the original top vector,
    Federer 4.1.6, p. 352. *)
Definition field_duality_upper (K:fieldType) (h2:(1+1:K)!=0) (X:choiceType) (V:lmodType K)
    n (top:exterior_power V n) p (hp:(p<=n)%N):
    differential_form_space K X V K^o p->multivector_field_space K X V (n-p):=
  @pointwise_field_map K X (A_m V K^o p) (exterior_power V (n-p)) (@D_upper K V n h2 top p hp).

(** Source for [field_duality_upper_values]: pointwise
    D^p, Federer 4.1.6, p. 352. *)
Lemma field_duality_upper_values (K:fieldType) (h2:(1+1:K)!=0) (X:choiceType) (V:lmodType K)
    n (top:exterior_power V n) p (hp:(p<=n)%N) (phi:differential_form_space K X V K^o p) x:
  @multivector_field_value K X V (n-p) (field_duality_upper h2 top hp phi) x=
    D_upper h2 top hp (@differential_form_value K X V K^o p phi x).
Proof. exact:pointwise_field_map_values. Qed.

(** Source for [field_hodge_vector]: the original Hodge
    operation on a multivector field, Federer 4.1.6,
    p. 352, is the pointwise 1.7.8 operation. *)
Definition field_hodge_vector (R:realFieldType) (h2:(1+1:R)!=0) (X:choiceType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (top:exterior_power V n) p (hp:(p<=n)%N):
    multivector_field_space R X V p->multivector_field_space R X V (n-p):=
  @pointwise_field_map R X (exterior_power V p) (exterior_power V (n-p))
    (@hodge_vector R h2 V B hB n top p hp).

(** Source for [field_hodge_covector]: the original Hodge
    operation on a real form, Federer 4.1.6,
    p. 352, is the pointwise 1.7.8 operation. *)
Definition field_hodge_covector (R:realFieldType) (h2:(1+1:R)!=0) (X:choiceType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (top:exterior_power V n) p (hp:(p<=n)%N):
    differential_form_space R X V R^o p->differential_form_space R X V R^o (n-p):=
  @pointwise_field_map R X (A_m V R^o p) (A_m V R^o (n-p))
    (@hodge_covector R h2 V B hB n top p hp).
