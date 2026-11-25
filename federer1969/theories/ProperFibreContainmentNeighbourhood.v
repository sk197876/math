(** Federer (1969), 3.4.8(10), p. 332:
    nearby fibres stay in any open
    cover of one fibre when the
    fibres over a compact neighbourhood are
    compact. Reuse 2.10.26's compact residual-image
    proof rather than repeat the shrinking-intersection argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactFibreOpenCovers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [proper_fibre_containment_neighbourhood]:
    the residual set D_e is empty
    for some positive e, 3.4.8(10),
    p. 332. The equivalent compact-image
    argument retains empty fibres and arbitrary
    open source covers. *)
Theorem proper_fibre_containment_neighbourhood (R:realType) (X Y:metricType R)
    (P:X->Y) (Z O:set X) (C:set Y) (y:Y):
  continuous P ->nbhs y C ->
  compact [set x|Z x /\C (P x)] ->open O ->
  (forall x,Z x ->P x = y ->O x) ->
  nbhs y [set z|C z /\forall x,Z x ->P x = z ->O x].
Proof.
move=>hP hC hCompact hOpen hCover.
pose K:set X:=fun x=>Z x /\C (P x).
pose V:set Y:=fun z=>(K `&` P @^-1` [set z]) `<=` O.
have hVOpen:open V:=@compact_fibre_containment_open R X Y P K O hP hCompact hOpen.
have hy:V y.
  move=>x [[hx _] hEqual];exact:hCover x hx hEqual.
have hV:nbhs y V by move:hVOpen;rewrite openE=>h;exact:h y hy.
apply:filterS (filterI hC hV)=>z [hc hv];split;first exact:hc.
move=>x hx hEqual.
apply:hv;split;last exact:hEqual.
split;first exact:hx.
by rewrite hEqual.
Qed.
