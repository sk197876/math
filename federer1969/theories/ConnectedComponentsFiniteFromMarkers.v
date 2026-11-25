(** Federer (1969), 3.4.8(11), p. 333:
    each component of the positive set
    contains a component of the critical
    variety. A finite marker family therefore
    bounds the number of original components. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [components_finite_from_connected_markers]:
    the component-counting step for R and
    H in 3.4.8(11), p. 333.
    Markers are nonempty connected sets; their
    containment in an original component is
    proved by the caller from the positive
    critical value and the boundary condition. *)
Theorem components_finite_from_connected_markers (X:topologicalType)
    (A:set X) (F:set (set X)):
  finite_set F ->
  (forall B,F B ->connected B) ->
  (forall x,A x ->exists B,F B /\ B !=set0 /\
    B `<=` connected_component A x) ->
  finite_set (connected_component A @` A).
Proof.
move=>hF hConnected hMarker.
pose D:=F `&` [set B:set X|B !=set0 /\ B `<=` A].
have hD:finite_set D.
  apply:(sub_finite_set _ hF)=>B [hBF _];exact:hBF.
case:(pselect (exists x,A x))=>[[a ha]|hEmpty].
- pose r:=fun B:set X=>match pselect (exists x,B x) with
    | left h=>projT1 (cid h) | right _=>a end.
  have hr B:B !=set0 ->B (r B).
    move=>hB;rewrite /r;case:pselect=>[h|h];first exact:(projT2 (cid h)).
    exfalso;apply:h;exact:hB.
  have hFinite:finite_set ((fun B=>connected_component A (r B)) @` D).
    exact:finite_image hD.
  apply:(sub_finite_set _ hFinite)=>C [x hx <-].
  have [B [hBF [hBNonempty hBC]]]:=hMarker x hx.
  have hBA:B `<=` A.
    move=>z hz;exact:(@connected_component_sub X A x z (hBC z hz)).
  exists B;first by split;last split.
  apply:esym;apply:same_connected_component;exact:hBC (r B) (hr B hBNonempty).
- have hA:A = set0 by apply/seteqP;split=>x hx;[exfalso;apply:hEmpty;exists x|].
  by rewrite hA image_set0;exact:finite_set0.
Qed.
