(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8),
    pp. 326, 329: the full original prefix is a coordinate
    isomorphism. The original basis and dual equations suffice. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom TensorUP LinearBasis FiniteCoordinates FieldPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_full_prefix_inverse]: the original full
    prefix and its section compose to the identity, including
    dimension zero, 3.4.8(1),(8), pp. 326, 329. *)
Theorem field_full_prefix_inverse (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X K^o)
    (P:Hom X (coordinate_space K n)) (S:Hom (coordinate_space K n) X):
  (forall i j,omega i (e j)=if i==j then 1 else 0) ->
  is_field_prefix_projection omega (leqnn n) P ->
  is_field_prefix_section e (leqnn n) S ->forall x,S (P x)=x.
Proof.
move=>hDual hP hS.
apply:(@basis_linear_ext K 'I_n X e he X (hom_as_linear (hom_comp S P)) (linear_id X))=>i.
have hPi:P (e i)=@coordinate_basis K n i.
  apply/ffunP=>j;rewrite hP hDual /coordinate_basis ffunE.
  have hWiden:widen_ord (leqnn n) j=j by apply:val_inj.
  by rewrite hWiden eq_sym.
rewrite hom_as_linearE hom_compE hPi hS.
have hWiden:widen_ord (leqnn n) i = i by apply:val_inj.
by rewrite hWiden.
Qed.
