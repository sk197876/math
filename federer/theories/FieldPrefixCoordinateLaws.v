(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    the original coordinate equations determine the prefix
    maps uniquely. The dual-basis equations prove the
    actual section relation, including empty prefixes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import TensorUP Hom LinearBasis FiniteCoordinates FieldPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_prefix_projection_unique]: the original
    coordinate equation determines p_j, supporting
    3.4.8(1), p. 326. *)
Lemma field_prefix_projection_unique (K:fieldType) (X:lmodType K) n
    (omega:'I_n->Hom X K^o) j (hjn:(j<=n)%N) (P Q:Hom X (coordinate_space K j)):
  is_field_prefix_projection omega hjn P ->is_field_prefix_projection omega hjn Q ->P=Q.
Proof.
move=>hP hQ;apply:hom_ext=>x;apply/ffunP=>i.
by rewrite hP hQ.
Qed.

(** Source for [field_prefix_section_unique]: values on
    the original coordinate basis determine the auxiliary
    inclusion, supporting 3.4.8(1),(5), pp. 326, 328. *)
Lemma field_prefix_section_unique (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) j (hjn:(j<=n)%N) (S T:Hom (coordinate_space K j) X):
  is_field_prefix_section e hjn S ->is_field_prefix_section e hjn T ->S=T.
Proof.
move=>hS hT;apply:hom_ext.
apply:(@basis_linear_ext K (Choice.clone 'I_j _) (coordinate_space K j) (@coordinate_basis K j)
  (@coordinate_basisP K j) X (hom_as_linear S) (hom_as_linear T))=>i.
by rewrite !hom_as_linearE hS hT.
Qed.

(** Source for [field_prefix_projection_section]: the dual
    original bases make the prefix inclusion a section
    of p_j, supporting the coordinate subring and its
    closedness in 3.4.8(1),(5), pp. 326, 328. *)
Theorem field_prefix_projection_section (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (omega:'I_n->Hom X K^o) j (hjn:(j<=n)%N)
    (P:Hom X (coordinate_space K j)) (S:Hom (coordinate_space K j) X):
  (forall i k,omega i (e k)=if i==k then 1 else 0) ->
  is_field_prefix_projection omega hjn P ->is_field_prefix_section e hjn S ->
  forall z,P (S z)=z.
Proof.
move=>hDual hP hS.
apply:(@basis_linear_ext K (Choice.clone 'I_j _) (coordinate_space K j) (@coordinate_basis K j)
  (@coordinate_basisP K j) (coordinate_space K j) (hom_as_linear (hom_comp P S)) (linear_id (coordinate_space K j)))=>i.
rewrite hom_as_linearE hom_compE hS.
apply/ffunP=>k.
rewrite hP hDual /coordinate_basis ffunE.
by rewrite -!val_eqE /=.
Qed.
