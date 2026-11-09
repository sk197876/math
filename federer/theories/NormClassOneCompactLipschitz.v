(** Federer (1969), 3.4.2(8), p. 315: a class-one map
    into an arbitrary normed space has a finite Lipschitz bound
    on a compact subset of its original open domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormClassOneUP
  NormClassOneLocalLipschitz NormCompactFunctionBound MetricCompactLocalLipschitz
  CoveringFamilyUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_one_compact_lipschitz]: the choice
    of a common Lipschitz constant for g and f composed with g
    in 3.4.2(8), p. 315. Local derivative bounds and compact
    image bounds give a finite global bound on the compact set.
    The proof uses the given norm; the target need not carry
    an inner product, be complete, or have finite dimension. *)
Theorem norm_class_one_compact_lipschitz (R:realType)
    (V W:lmodType R) (NV:V->R) (NW:W->R)
    (hV:is_real_norm NV) (hW:is_real_norm NW)
    (U K:set V) (f:V->W):
  norm_class_one NV NW U f ->K `<=` U ->
  @compact (real_norm_metric_space hV) K ->
  @is_metric_lipschitz R (real_norm_metric_space hV)
    (real_norm_metric_space hW) K f.
Proof.
move=>hClass hKU hK.
have [D hD]:=hClass.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R V W NV NW hV hW
  U K f hK hKU (norm_class_one_zero hD).
apply:(@metric_compact_local_lipschitz R (real_norm_metric_space hV)
  (real_norm_metric_space hW) K f (M+M) hK (addr_ge0 (ltW hM) (ltW hM))).
- move=>x y hx hy;rewrite real_norm_metric_distanceE.
  have hTriangle:=real_seminorm_triangle hW.1 (f x) (-f y).
  rewrite (real_seminorm_negate hW.1) in hTriangle.
  exact:le_trans hTriangle (lerD (hBound x hx) (hBound y hy)).
- move=>c hc.
  have [L [r [hL [hr [hDomain hLocal]]]]]:=
    @norm_class_one_local_lipschitz R V W NV NW hV hW U f c (hKU c hc) hClass.
  exists r,L;split;first exact:hr.
  split;first exact:ltW hL.
  move=>x y hx hy;rewrite real_norm_metric_distanceE.
  have hxSmall:NV (x-c)<r by rewrite (real_seminorm_subtract hV.1);exact:hx.
  have hySmall:NV (y-c)<r by rewrite (real_seminorm_subtract hV.1);exact:hy.
  exact:hLocal x y hxSmall hySmall.
Qed.
