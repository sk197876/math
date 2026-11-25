(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: adjacent original prefix projections compose.
    This coordinate identity depends only on the field laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom FiniteCoordinates FieldCoordinateFunctional FieldPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [field_adjacent_prefix_composition]: the nested
    coordinate equation underlying the original Q_j tower,
    3.4.8(8), p. 329. *)
Theorem field_adjacent_prefix_composition (K:fieldType) (X:lmodType K) n
  (omega:'I_n->Hom X K^o) j (hJN:(j<=n)%N) (hJ1N:(j.+1<=n)%N)
  (P:Hom X (coordinate_space K j)) (Q:Hom X (coordinate_space K j.+1))
  (between:Hom (coordinate_space K j.+1) (coordinate_space K j)):
  is_field_prefix_projection omega hJN P ->is_field_prefix_projection omega hJ1N Q ->
  is_field_prefix_projection (fun i:'I_j.+1=>field_coordinate_functional i) (leqnSn j) between ->
  forall x:X,P x=between (Q x).
Proof.
move=>hP hQ hBetween x;apply/ffunP=>i.
rewrite hP hBetween.
change (omega (widen_ord hJN i) x=Q x (widen_ord (leqnSn j) i)).
rewrite hQ.
have hIndex:widen_ord hJN i=widen_ord hJ1N (widen_ord (leqnSn j) i) by apply:val_inj.
by rewrite hIndex.
Qed.
