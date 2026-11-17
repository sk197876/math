(** Federer (1969), 3.4.8(10), p. 332:
    each continuous ordered inverse section
    has relatively open image in Z.
    Use its actual local inverse chart
    and the proved neighbourhood criterion. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import EuclideanSubmanifoldUP RelativeLocalInverseUP RelativeOpenLocalNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_local_inverse_sheet_open]:
    the sets im(psi_lambda) are relatively
    open in Z, 3.4.8(10),
    p. 332. Continuity keeps the
    section inside one original inverse chart;
    its cancellation law then identifies every
    nearby point of Z with the section. *)
Theorem continuous_local_inverse_sheet_open (X Y:topologicalType)
    (P:X->Y) (Z:set X) (V:set Y) (psi:Y->X):
  continuous P ->open V ->
  (forall y,V y ->{for y,continuous psi}) ->
  (forall y,V y ->Z (psi y) /\P (psi y) = y) ->
  (forall x,Z x ->exists U W eta,is_relative_local_inverse P Z x U W eta) ->
  relatively_open_set Z (psi @` V).
Proof.
move=>hP hOpen hContinuous hMaps hCharts.
apply:relative_open_local_neighbourhood.
- move=>x [y hy <-];exact:(hMaps y hy).1.
- move=>x [y hy <-].
  have [U [W [eta [hUy [hUOpen [hWOpen [hWAt [hEtaMaps [hEtaInverse hEtaContinuous]]]]]]]]]:=
    hCharts (psi y) (hMaps y hy).1.
  have hUNear:nbhs (psi y) U by have h:=hUOpen;rewrite openE in h;exact:h _ hUy.
  have hPsiNear:nbhs y (psi @^-1` U):=hContinuous y hy U hUNear.
  have hVNear:nbhs y V by rewrite openE in hOpen;exact:hOpen y hy.
  have hTarget:nbhs (P (psi y)) (V `&` psi @^-1` U).
    rewrite (hMaps y hy).2;exact:filterI hVNear hPsiNear.
  have hPre:nbhs (psi y) (P @^-1` (V `&` psi @^-1` U)):=hP (psi y) _ hTarget.
  apply:filterS (filterI hUNear hPre)=>z [hUz [hVz hUPsi]] hz.
  exists (P z);first exact:hVz.
  have hPoint:=hMaps (P z) hVz.
  have hInverse:eta (P z) = psi (P z).
    have h:=hEtaInverse (psi (P z)) hPoint.1 hUPsi.
    by rewrite hPoint.2 in h.
  rewrite -hInverse;exact:hEtaInverse z hz hUz.
Qed.
