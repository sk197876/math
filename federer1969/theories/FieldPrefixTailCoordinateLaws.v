(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332:
    the original suffix basis lies in
    ker(p_m), with the original dual
    coordinate equations. Apply the prefix
    specification and finite ordinal tail laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates FieldPrefixCoordinatesUP OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TailCoordinates.
Variable R:fieldType.
Variable X:lmodType R.
Variable n:nat.
Variable e:'I_n->X.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable m:nat.
Hypothesis hMN:(m<=n)%N.
Variable P:Hom X (coordinate_space R m).
Hypothesis hP:is_field_prefix_projection omega hMN P.

(** Source for [field_prefix_original_tail_zero]:
    p_m(e_j)=0 for j>m in
    the displayed differential calculation,
    3.4.12, p. 339, extending 3.4.8(10), pp. 331–332. *)
Lemma field_prefix_original_tail_zero (j:'I_(n-m)):
  P (e (ordinal_coordinate_tail_index hMN j)) = 0.
Proof.
apply/ffunP=>i.
rewrite hP hDual ffunE.
have hDifferent:widen_ord hMN i !=ordinal_coordinate_tail_index hMN j.
  apply/eqP=>hEqual.
  have hValue:=congr1 (fun q:'I_n=>(q:nat)) hEqual.
  change ((i:nat)=(m+j)%N) in hValue.
  have hLess:(m+j<m)%N by rewrite -hValue;exact:ltn_ord i.
  have hLower:(m<=m+j)%N by rewrite leq_addr.
  have hImpossible:=leq_ltn_trans hLower hLess;by rewrite ltnn in hImpossible.
by rewrite (negbTE hDifferent).
Qed.

(** Source for [field_original_tail_duality]:
    the original suffix covectors and basis
    retain their Kronecker pairing, supporting
    3.4.12, p. 339, extending 3.4.8(10), pp. 331–332. *)
Lemma field_original_tail_duality (i j:'I_(n-m)):
  omega (ordinal_coordinate_tail_index hMN i) (e (ordinal_coordinate_tail_index hMN j)) =
    if i==j then 1 else 0.
Proof.
by rewrite hDual (inj_eq (@ordinal_coordinate_tail_injective n m hMN)).
Qed.
End TailCoordinates.
