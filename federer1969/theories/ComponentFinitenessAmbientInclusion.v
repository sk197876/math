(** Federer (1969), 3.4.8(11), p. 333:
    counting components of local strata bounds
    the ambient components which meet them.
    Enlarging the original set can join
    connected components; it cannot create more
    components meeting the original smaller set. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [component_finiteness_ambient_inclusion]:
    the local finite component cover controls
    actual components of H near a
    point, 3.4.8(11), p. 333.
    This supporting theorem counts only ambient
    components meeting the original smaller set. *)
Theorem component_finiteness_ambient_inclusion (X:topologicalType) (A B:set X):
  B `<=` A ->finite_set (connected_component B @` B) ->
  finite_set (connected_component A @` B).
Proof.
move=>hBA hFinite.
case:(pselect (exists x,B x))=>[[a ha]|hEmpty].
- pose r:=fun C:set X=>match pselect (exists x,C x) with
    | left h=>projT1 (cid h) | right _=>a end.
  have hr C:(exists x,C x) ->C (r C).
    move=>hC;rewrite /r;case:pselect=>[h|h];first exact:(projT2 (cid h)).
    exfalso;exact:h hC.
  have hImageFinite:finite_set ((fun C=>connected_component A (r C)) @`
    (connected_component B @` B)):=finite_image _ hFinite.
  apply:(sub_finite_set _ hImageFinite)=>C [x hx <-].
  pose D:=connected_component B x.
  have hDx:D x:=connected_component_refl hx.
  have hDr:D (r D):=hr D (ex_intro _ x hDx).
  have hDA:D `<=` A.
    move=>z hz;exact:hBA z (@connected_component_sub X B x z hz).
  have hRelated:connected_component A x (r D).
    exact:(@connected_component_max X A D x hDx hDA (@component_connected X B x) (r D) hDr).
  exists D;first by exists x.
  exact:esym (@same_connected_component X A x (r D) hRelated).
- have hB:B = set0 by apply/seteqP;split=>x hx;[exfalso;apply:hEmpty;exists x|].
  by rewrite hB image_set0;exact:finite_set0.
Qed.
