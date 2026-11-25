(** Private existence proof for the finite-at-each-point
    sum in Federer (1969), 3.1.13, p. 225. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp.
From Federer Require Import FiniteFamilySumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [finite_family_sum_exists]:
    existence of u(x)=sum_s u_s(x)
    in Federer 3.1.13, p. 225,
    once finite active selections are proved.
    A selected finite sum is independent
    of the selection by the abstract sum laws. *)
Theorem finite_family_sum_exists (X : Type) (J : choiceType) (Y : zmodType)
    (U : X->Prop) (I : J->Prop) (f : J->X->Y) :
  finite_active_family_on U I f ->
  exists g : X->Y, is_finite_family_sum_on U I f g.
Proof.
move=> hfin.
have hex x : exists y : Y, U x -> forall F : {fset J},
    (forall j, j \in F -> I j) ->
    (forall j, I j -> j \notin F -> f j x=0) ->
    y=\sum_(j <- F) f j x.
  case: (pselect (U x))=>[hx|hnx].
  - have [G [hGI hG]] := hfin x hx.
    exists (\sum_(j <- G) f j x)=>_ F hFI hF.
    exact: finite_family_sum_selection_independent hGI hFI hG hF.
  - exists 0=>hx; exfalso; exact: hnx hx.
have [g hg] := choice hex; by exists g.
Qed.
