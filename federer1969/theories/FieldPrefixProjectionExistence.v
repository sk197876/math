(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    the actual finite list of original coordinate
    functionals gives the projection specified by its laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom FiniteCoordinates FieldPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_prefix_projection_exists]: the
    original coordinate projection exists for every prefix,
    including dimension zero, 3.4.8(1), p. 326.
    The coordinate function is only an existence witness. *)
Theorem field_prefix_projection_exists (K:fieldType) (X:lmodType K) n
    (omega:'I_n->Hom X K^o) j (hjn:(j<=n)%N):
  exists P:Hom X (coordinate_space K j),is_field_prefix_projection omega hjn P.
Proof.
pose f (x:X):coordinate_space K j:=[ffun i=>omega (widen_ord hjn i) x].
have hLinear:linear f.
  move=>a x y;apply/ffunP=>i;rewrite /f !ffunE.
  exact:(hom_linear (omega (widen_ord hjn i)) a x y).
exists (@HomMap K X (coordinate_space K j) f (introT (asboolP _) hLinear))=>x i.
change (f x i=omega (widen_ord hjn i) x).
by rewrite /f ffunE.
Qed.
