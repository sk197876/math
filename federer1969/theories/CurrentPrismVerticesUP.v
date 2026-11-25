(** Federer (1969), 4.1.11, p. 366: the ordered
    vertices of the kth simplex in the prism formula.
    Specify the two original coordinate ranges before
    constructing or choosing any vertex family. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_current_prism_vertices]: the kth
    original family is (A(u_0),...,A(u_k),B(u_k),...,
    B(u_m)), supporting the displayed simplicial prism
    formula in Federer 4.1.11, p. 366. For the prism
    A(u)=(a,u) and B(u)=(b,u). No current identity
    or desired boundary assertion is included. *)
Definition is_current_prism_vertices (X Y:Type) (A B:X->Y)
    (P:forall m:nat,('I_(m.+1)->X)->'I_(m.+1)->'I_(m.+2)->Y):Prop:=
  (forall m (v:'I_(m.+1)->X) (k r:'I_(m.+1)),(r<=k)%N->
    P m v k (widen_ord (leqnSn m.+1) r)=A (v r)) /\
  (forall m (v:'I_(m.+1)->X) (k r:'I_(m.+1)),(k<=r)%N->
    P m v k (lift ord0 r)=B (v r)).

(** Source for [current_prism_widen_zero]: the original
    first vertex keeps index zero when the vertex family
    is enlarged, supporting Federer 4.1.11, p. 366. *)
Lemma current_prism_widen_zero m:
  widen_ord (leqnSn m.+1) (ord0:'I_(m.+1))=(ord0:'I_(m.+2)).
Proof. apply:val_inj;reflexivity. Qed.

(** Source for [current_prism_widen_lift]: deleting the
    original first index commutes with enlarging the
    vertex family, supporting Federer 4.1.11, p. 366. *)
Lemma current_prism_widen_lift m (r:'I_m):
  widen_ord (leqnSn m.+1) (lift (ord0:'I_(m.+1)) r)=
    lift (ord0:'I_(m.+2)) (widen_ord (leqnSn m) r).
Proof. apply:val_inj;reflexivity. Qed.

