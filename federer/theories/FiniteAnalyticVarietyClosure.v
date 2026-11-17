(** Federer (1969), 3.4.8(11), pp. 334–335:
    local containment in an analytic variety
    persists under closure inside the chosen open
    neighbourhood. Use the proved relatively closed
    representative of the original finite equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric FiniteAnalyticVarietyUP
  FiniteAnalyticVarietyRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_variety_local_closure]:
    the original containment of the regular closure
    in its analytic variety, used before choosing
    the nested radii, 3.4.8(11), p. 334.
    Containment is needed only on the original
    open neighbourhood, not on the whole ambient space. *)
Theorem finite_analytic_variety_local_closure (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U S W Z:set X):
  @is_finite_analytic_variety R X NX hNX U S ->
  @open (real_norm_metric_space hNX) W ->W `<=` U ->
  (forall x,Z x ->W x ->S x) ->
  W `&` @closure (real_norm_metric_space hNX) Z `<=` S.
Proof.
move=>hVariety hW hWU hZS.
have [C [hC hS]]:=finite_analytic_variety_relative_closed_form hVariety.
move=>x [hWx hClosure];rewrite hS;split;first exact:hWU x hWx.
apply:contrapT=>hNotC.
have hOpen:@open (real_norm_metric_space hNX) (W `&` ~` C):=openI hW (closed_openC hC).
have hNear:(nbhs (x:real_norm_metric_space hNX)) (W `&` ~` C).
  move:hOpen;rewrite openE;apply;by split.
have [z [hZz [hWz hNotCz]]]:=hClosure (W `&` ~` C) hNear.
apply:hNotCz;have hSz:=hZS z hZz hWz;by rewrite hS in hSz;exact:hSz.2.
Qed.
