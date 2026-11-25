(** Federer (1969), 3.4.1, p. 310: opaque critical degree, exposed only by its printed equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import CriticalValueDegreeUP CriticalValueDegreeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CriticalValueDegreeSignature.
(** Source for [value]: the critical scalar of 3.4.1, p. 310, for
    exactly the printed integer range k>=1 and m>nu>=0. *)
Parameter value:forall (R:realType) (m nu k:nat),(0<k)%N ->(nu<m)%N ->R.
(** Source for [laws]: the independent printed degree equation from
    3.4.1, p. 310. No Hausdorff-nullity conclusion is supplied as a law. *)
Parameter laws:forall R m nu k hk hnu,is_critical_value_degree m nu k (@value R m nu k hk hnu).
End CriticalValueDegreeSignature.
Module CriticalValueDegree:CriticalValueDegreeSignature.
(** Source for [value]: the existence witness for the printed scalar,
    3.4.1, p. 310. This implementation is hidden by the opaque seal. *)
Definition value (R:realType) m nu k (hk:(0<k)%N) (hnu:(nu<m)%N):=
  projT1 (cid (@critical_value_degree_exists R m nu k)).
(** Source for [laws]: the private witness satisfies the independent
    degree equation of 3.4.1, p. 310. *)
Lemma laws R m nu k hk hnu:is_critical_value_degree m nu k (@value R m nu k hk hnu).
Proof. exact:(projT2 (cid (@critical_value_degree_exists R m nu k))). Qed.
End CriticalValueDegree.
