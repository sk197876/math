(** Federer (1969), 3.1.22, p. 236: multiplying
    a locally finite partition by local extension values does
    not enlarge the set of active terms. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_locally_finite_zero_transfer]: supporting
    local finiteness of weighted local extensions in Federer
    3.1.22, p. 236, via 3.1.13, p. 225.
    The same finite active selection works for any second
    family which vanishes wherever the partition term vanishes. *)
Lemma norm_locally_finite_zero_transfer (R:realType) (X:lmodType R)
    (Y V:zmodType) (J:choiceType) (NX:X->R) (U:X->Prop) (I:J->Prop)
    (u:J->X->Y) (v:J->X->V) :
  is_norm_locally_finite_function_family NX U I u ->
  (forall j,I j -> forall x,U x -> u j x=0 -> v j x=0) ->
  is_norm_locally_finite_function_family NX U I v.
Proof.
move=>hloc hz a ha.
have [O [hOa [hOU [hOint [F [hFI hF]]]]]]:=hloc a ha.
exists O; split=>//; split=>//; split=>//.
exists F; split=>// x hx j hj hnot.
exact (hz j hj x (hOU x hx) (hF x hx j hj hnot)).
Qed.
