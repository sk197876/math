(** Federer (1969), 4.1.7, p. 358: the
    opaque global comass of an original form.
    Clients use only the independently specified
    least-upper-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP GrassmannAbbreviations AlternatingForms
  CurrentGlobalComassUP CurrentGlobalComassExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentGlobalComassSignature.
(** Source for [value]: the original global
    form comass, Federer 4.1.7, p. 358. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n m
  (U:set (R_n R n)),(R_n R n->A_m (R_n R n) R^o m)->\bar R.
(** Source for [laws]: the original pointwise
    supremum specification, Federer 4.1.7, p. 358. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n m
  (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m),
  @is_current_global_comass R h2 n m U phi (@value R h2 n m U phi).
End CurrentGlobalComassSignature.
Module CurrentGlobalComass:CurrentGlobalComassSignature.
(** Source for [value]: hide the proved
    supremum witness, supporting Federer 4.1.7,
    p. 358. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m): \bar R:=
  projT1 (cid (@current_global_comass_exists R h2 n m U phi)).
(** Source for [laws]: the hidden value
    satisfies the independent original comass laws,
    supporting Federer 4.1.7, p. 358. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m):
  @is_current_global_comass R h2 n m U phi (@value R h2 n m U phi).
Proof. exact:(projT2 (cid (@current_global_comass_exists R h2 n m U phi))). Qed.
End CurrentGlobalComass.
