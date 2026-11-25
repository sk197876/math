(** Federer (1969), 4.1.25, p. 383: hide
    the choice of the proved bounded smooth approximation.
    Consumers use its independently stated approximation laws;
    the convolution construction serves only as existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness CurrentLipschitzLebesgueActionFamilyUP
  CurrentLipschitzLebesgueActionFamilyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentLipschitzLebesgueActionFamilySignature.
(** Source for [value]: the actual chosen smooth
    sequence used in the proof of 4.1.25, p. 383. *)
Parameter value : forall (R:realType) m n
    (f:R_n R m->R_n R n) (L:R)
    (hL:0<=L)
    (hLip:forall x y,
      inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
        L*inner_norm (@euclidean_inner_productP R m) (x-y)),
  nat->R_n R m->R_n R n.
(** Source for [laws]: the full bounded approximation
    and actual-graph differential limits of 4.1.25, p. 383. *)
Parameter laws : forall (R:realType) m n
    (f:R_n R m->R_n R n) (L:R)
    (hL:0<=L)
    (hLip:forall x y,
      inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
        L*inner_norm (@euclidean_inner_productP R m) (x-y)),
  is_current_lipschitz_lebesgue_action_family f L
    (@value R m n f L hL hLip).
End CurrentLipschitzLebesgueActionFamilySignature.

Module CurrentLipschitzLebesgueActionFamily :
    CurrentLipschitzLebesgueActionFamilySignature.
(** Source for [value]: choose the already proved
    witness for the first proof of 4.1.25, p. 383. *)
Definition value (R:realType) m n
    (f:R_n R m->R_n R n) (L:R)
    (hL:0<=L)
    (hLip:forall x y,
      inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
        L*inner_norm (@euclidean_inner_productP R m) (x-y)) :
    nat->R_n R m->R_n R n :=
  projT1 (cid (@current_lipschitz_lebesgue_action_family_exists R m n f L hL hLip)).
(** Source for [laws]: the hidden witness has exactly
    the independently specified laws of 4.1.25, p. 383. *)
Lemma laws (R:realType) m n
    (f:R_n R m->R_n R n) (L:R)
    (hL:0<=L)
    (hLip:forall x y,
      inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
        L*inner_norm (@euclidean_inner_productP R m) (x-y)) :
  is_current_lipschitz_lebesgue_action_family f L
    (@value R m n f L hL hLip).
Proof.
exact:(projT2 (cid (@current_lipschitz_lebesgue_action_family_exists
  R m n f L hL hLip))).
Qed.
End CurrentLipschitzLebesgueActionFamily.
Arguments CurrentLipschitzLebesgueActionFamily.value : clear implicits.
Arguments CurrentLipschitzLebesgueActionFamily.laws : clear implicits.
