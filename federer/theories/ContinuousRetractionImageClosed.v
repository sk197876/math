(** Federer (1969), 3.4.8(5), p. 328:
    the original coordinate germ subring is closed.
    A continuous retraction identifies an embedded image
    with a closed equalizer. This general-topology argument
    supplies an alternative to the printed jet criterion. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_retraction_image_closed]: the
    image of a continuous section with a continuous
    retraction is closed in a Hausdorff target,
    supporting the coordinate subring in 3.4.8(5), p. 328. *)
Theorem continuous_retraction_image_closed (T U:topologicalType) (f:T->U) (r:U->T):
  hausdorff_space U ->continuous f ->continuous r ->
  (forall x,r (f x)=x) ->closed (f @` setT).
Proof.
move=>hU hf hr hSection.
have hEqual:f @` setT = [set y|f (r y)=y].
  apply/seteqP;split.
  - move=>y [x _ <-];by rewrite /= hSection.
  - move=>y hy;exists (r y);[exact:Logic.I|exact:hy].
rewrite hEqual.
apply:(@continuous_equalizer_closed U U (fun y=>f (r y)) (fun y=>y) hU).
- move=>y A hA;exact:(hr y _ (hf (r y) A hA)).
- by move=>y A hA.
Qed.
