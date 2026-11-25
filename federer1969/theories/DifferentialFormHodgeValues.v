(** Federer (1969), 4.1.6, p. 352: the
    original Hodge operations have exactly the
    pointwise values stated in the book. Use the
    opaque field evaluation laws and the public
    Chapter 1 Hodge maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom InnerProductUP ExteriorGrading AlternatingForms HodgeMaps
  PointwiseFieldSpaceSealed PointwiseFieldMaps DifferentialFormFields DifferentialFormDuality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [field_hodge_vector_values]: *xi(x)
    is the original * applied to xi(x),
    Federer 4.1.6, p. 352. *)
Lemma field_hodge_vector_values (R:realFieldType) (h2:(1+1:R)!=0) (X:choiceType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (top:exterior_power V n) p (hp:(p<=n)%N)
    (xi:multivector_field_space R X V p) x:
  @multivector_field_value R X V (n-p) (@field_hodge_vector R h2 X V B hB n top p hp xi) x=
    @hodge_vector R h2 V B hB n top p hp (@multivector_field_value R X V p xi x).
Proof. exact:pointwise_field_map_values. Qed.

(** Source for [field_hodge_covector_values]: *phi(x)
    is the original * applied to phi(x),
    Federer 4.1.6, p. 352. *)
Lemma field_hodge_covector_values (R:realFieldType) (h2:(1+1:R)!=0) (X:choiceType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (top:exterior_power V n) p (hp:(p<=n)%N)
    (phi:differential_form_space R X V R^o p) x:
  @differential_form_value R X V R^o (n-p) (@field_hodge_covector R h2 X V B hB n top p hp phi) x=
    @hodge_covector R h2 V B hB n top p hp (@differential_form_value R X V R^o p phi x).
Proof. exact:pointwise_field_map_values. Qed.
