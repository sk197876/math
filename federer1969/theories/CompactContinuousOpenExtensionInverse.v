(** Federer (1969), 4.1.5, pp. 349–350:
    restricting an original zero-normalized field to U
    and extending it back by zero changes no value.
    This supplies the exact agreement on original tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import CompactContinuousVectorZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_vector_open_extension_restriction_inverse]:
    the original field is unchanged by restriction and
    zero extension, for the extension of S in Federer
    4.1.5, pp. 349–350. *)
Theorem compact_vector_open_extension_restriction_inverse (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (w:X->Y):
  (forall x,~U x ->w x=0) ->
  @compact_vector_open_extension R X U Y (fun x=>w (set_val x))=w.
Proof.
move=>hOff; apply:funext=>x; case:(pselect (U x))=>hx.
- pose z:set_type U:=exist _ x (mem_set hx).
  exact:(@compact_vector_open_extension_value R X U Y (fun y=>w (set_val y)) z).
- by rewrite (@compact_vector_open_extension_outside R X U Y (fun y=>w (set_val y)) x hx)
    (hOff x hx).
Qed.
