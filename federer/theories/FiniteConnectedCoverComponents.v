(** Federer (1969), 3.4.8(11), pp. 333–335:
    a finite connected cover has only finitely
    many components. This supporting topology
    lemma retains the original ambient topology. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_connected_cover_components]:
    assemble finite connected pieces into the
    component finiteness used in 3.4.8(11),
    pp. 333–335. Empty pieces and the
    empty original set are allowed. *)
Theorem finite_connected_cover_components (X:topologicalType) (A:set X) (F:set (set X)):
  finite_set F ->
  (forall C,F C ->C `<=` A /\ connected C) ->
  (forall x,A x ->exists C,F C /\ C x) ->
  finite_set (connected_component A @` A).
Proof.
move=>hF hPieces hCover.
case:(pselect (exists x,A x))=>[[a ha]|hEmpty].
- pose r:=fun C:set X=>match pselect (exists x,C x) with
    | left h=>projT1 (cid h) | right _=>a end.
  have hr C:(exists x,C x) ->C (r C).
    move=>hC;rewrite /r;case:pselect=>[h|h];first exact:(projT2 (cid h)).
    exfalso;exact:h hC.
  have hFinite:finite_set ((fun C=>connected_component A (r C)) @` F).
    exact:finite_image hF.
  apply:(sub_finite_set _ hFinite)=>C [x hx <-].
  have [S [hSF hSx]]:=hCover x hx.
  have hSr:S (r S):=hr S (ex_intro _ x hSx).
  have hRelated:connected_component A x (r S).
    exact:(@connected_component_max X A S x hSx (hPieces S hSF).1
      (hPieces S hSF).2 (r S) hSr).
  exists S;first exact:hSF.
  exact:esym (@same_connected_component X A x (r S) hRelated).
- have hA:A = set0 by apply/seteqP;split=>x hx;[exfalso;apply:hEmpty;exists x|].
  rewrite hA image_set0;exact:finite_set0.
Qed.
