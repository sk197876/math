(** Federer (1969), 3.3.20, pp. 307–308:
    actual original Cantor limits are transported by positive similarities. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  AffineIntervalTransportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_tree_limit_positive_affine_transport]:
    supporting ACTUAL original-limit similarity in
    3.3.20, pp. 307–308. The same
    fixed inverse scalar coordinate belongs to every
    original level. Thus the image of the original
    intersection is exactly the limit of the original
    image levels. No independently selected replacement
    Cantor set, measure identity or limit premise is used. *)
Theorem interval_tree_limit_positive_affine_transport (R:realType) (a r:R) M
    (H:nat->{fset compact_real_intervals R}) (A:set (real_line_metric R)):
  0<r ->is_affine_interval_transport a r M ->is_special_interval_tree_limit H A ->
  is_special_interval_tree_limit (fun j=>[fset M S|S in H j]) ((fun x:R=>a+r * x) @` A).
Proof.
move=>hr hM hA y;split.
- move=>[x hx hValue] j.
  have [S [hS hxS]]:=(hA x).1 hx j.
  exists (M S);split;first by apply/imfsetP;exists S.
  rewrite hM;exists x=>//.
- move=>hLevels.
  pose x:=(y-a)/r.
  have hNZ:r!=0 by rewrite gt_eqF.
  have hCancel:a+r * x=y by rewrite /x;field;by rewrite hNZ.
  have hOriginal:A x.
    apply:(hA x).2=>j.
    have [T [/imfsetP[S hS hT] hyT]]:=hLevels j.
    rewrite hT hM in hyT.
    have [z hz hValue]:=hyT.
    have hZX:z=x.
      apply:(mulfI hNZ);apply:(addrI a).
      by rewrite hCancel.
    exists S;split=>//;by rewrite -hZX.
  exists x=>//.
Qed.
