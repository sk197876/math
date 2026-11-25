(** Federer (1969), 3.4.8(11), pp. 333–335:
    the original continuous coordinate change preserves
    equality of set germs at the corresponding centres.
    Pull back the actual equality neighbourhood; no
    new representative or germ operation is selected. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_continuous_preimage_equality]:
    return the original exact germ union from
    rotated coordinates in 3.4.8(11), pp. 333–335.
    Continuity at all points is sufficient; invertibility
    is needed separately for the geometric conclusions. *)
Theorem set_germ_continuous_preimage_equality (X Y:topologicalType) (u:X->Y) a b (S T:set Y):
  continuous u ->u a = b ->@set_germ Y b S = @set_germ Y b T ->
  @set_germ X a (u @^-1` S) = @set_germ X a (u @^-1` T).
Proof.
move=>hU hCentre /set_germ_equality_original [W [hW [hWb hEqual]]].
apply/set_germ_equality_original;exists (u @^-1` W);split.
- exact:(@open_comp X Y u W (fun x _=>hU x) hW).
split;first by change (W (u a));rewrite hCentre.
apply/seteqP;split.
- move=>x [hSx hWx];split;last exact:hWx.
  have hMember:(T `&` W) (u x) by rewrite -hEqual;split.
  exact:hMember.1.
- move=>x [hTx hWx];split;last exact:hWx.
  have hMember:(S `&` W) (u x) by rewrite hEqual;split.
  exact:hMember.1.
Qed.
