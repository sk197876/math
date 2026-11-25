(** Federer (1969), 4.1.1, p. 343: opaque exact suprema
    of linear derivative observations. Only the value and its
    independently stated least-bound laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearObservationSeminormUP
  LinearObservationSeminormExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type LinearObservationSeminormSignature.
(** Source for [value]: the exact finite supremum supporting
    nu^i_K in Federer 4.1.1, p. 343. *)
Parameter value : forall (R:realType) (E:lmodType R) (I:Type)
    (W:I->lmodType R) (N:forall i,W i->R) (L:forall i,Hom E (W i)),
    (forall i,is_real_seminorm (@N i)) ->
    (forall f,exists C:R,0<=C /\ forall i,@N i (@L i f)<=C) -> E->R.
(** Source for [laws]: the exact supremum satisfies the independent
    observation-norm specification, Federer 4.1.1, p. 343. *)
Parameter laws : forall (R:realType) (E:lmodType R) (I:Type)
    (W:I->lmodType R) (N:forall i,W i->R) (L:forall i,Hom E (W i))
    (hN:forall i,is_real_seminorm (@N i))
    (hb:forall f,exists C:R,0<=C /\ forall i,@N i (@L i f)<=C),
    is_linear_observation_seminorm N L (@value R E I W N L hN hb).
End LinearObservationSeminormSignature.

Module LinearObservationSeminorm : LinearObservationSeminormSignature.
(** Source for [value]: privately select the proved supremum
    witness supporting Federer 4.1.1, p. 343. *)
Definition value (R:realType) (E:lmodType R) (I:Type)
    (W:I->lmodType R) (N:forall i,W i->R) (L:forall i,Hom E (W i))
    (hN:forall i,is_real_seminorm (@N i))
    (hb:forall f,exists C:R,0<=C /\ forall i,@N i (@L i f)<=C) : E->R :=
  projT1 (cid (linear_observation_seminorm_exists hN hb)).
(** Source for [laws]: the privately proved supremum laws,
    supporting Federer 4.1.1, p. 343. *)
Lemma laws (R:realType) (E:lmodType R) (I:Type)
    (W:I->lmodType R) (N:forall i,W i->R) (L:forall i,Hom E (W i))
    (hN:forall i,is_real_seminorm (@N i))
    (hb:forall f,exists C:R,0<=C /\ forall i,@N i (@L i f)<=C) :
    is_linear_observation_seminorm N L (@value R E I W N L hN hb).
Proof. exact:(projT2 (cid (linear_observation_seminorm_exists hN hb))). Qed.
End LinearObservationSeminorm.
