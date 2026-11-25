(** Federer (1969), 4.1.15, p. 372: the actual smoothings
    of the ambient comparison maps take one common neighbourhood
    of K into the original open target. This supporting compactness
    argument retains the given approximation sequence. Neither the
    ambient map nor any approximant must map all of the source
    into V. The compact set and target may be empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormClassZeroTopology
  NormClassHigherRestriction NormOpenPreimage SmoothCompactSet
  MetricOpenThickening MetricOpenThickeningClosure MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_compact_uniform_image_neighbourhood]:
    preserve the actual smooth approximation families used in
    Federer 4.1.15, p. 372, on one open neighbourhood of the
    original compact K. Compactness gives a positive target
    margin, and uniform convergence uses half of that margin.
    No completeness, finite dimension or global V-image is assumed. *)
Theorem norm_compact_uniform_image_neighbourhood
    (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (V:set Y)
    (hU:forall x,U x->norm_domain_interior NX U x)
    (hV:forall y,V y->norm_domain_interior NY V y)
    (K:smooth_compact_set hNX U) (F:X->Y) (a:nat->X->Y):
  norm_class_zero NX NY setT F->
  (forall x,smooth_compact_carrier K x->V (F x))->
  (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,NY (a i x-F x)<eps)->
  exists Z:set X,
    (forall x,Z x->norm_domain_interior NX Z x) /\
    smooth_compact_carrier K `<=` Z /\ Z `<=` U /\
    (smooth_compact_carrier K=set0->Z=set0) /\
    exists N:nat,forall i:nat,(N<=i)%N->forall x,Z x->V (a i x).
Proof.
move=>hContinuous hImageK hUniform.
pose XT:=real_norm_metric_space hNX.
pose YT:=real_norm_metric_space hNY.
have hTopology:continuous (fun x:XT=>(F x:YT)).
  move=>x;exact:(@norm_class_zero_continuous_at R X Y NX NY
    hNX hNY setT F x hContinuous Logic.I).
have hImageCompact:@compact YT (F @` smooth_compact_carrier K).
  exact:continuous_compact (continuous_subspaceT hTopology)
    (smooth_compact_is_compact K).
have hVOpen:@open YT V.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY V y).1
    (@hV y hy).
have hContained:F @` smooth_compact_carrier K `<=` V.
  move=>y [x hx <-];exact:(@hImageK x hx).
have[d [hd hTube]]:=@compact_metric_open_thickening R YT
  (F @` smooth_compact_carrier K) V hImageCompact hVOpen hContained.
have hHalf:0<d/2 by rewrite divr_gt0 // ltr0n.
pose W:set Y:=@metric_open_thickening R YT
  (F @` smooth_compact_carrier K) (d/2).
pose Z:set X:=[set x|U x /\ W (F x)].
have hRestricted:norm_class_zero NX NY U F.
  exact:(@norm_class_zero_open_restriction R X Y NX NY setT U F
    (fun _ _=>Logic.I) hU hContinuous).
have hWOpen:@open YT W.
  exact:(@metric_open_thickening_open R YT
    (F @` smooth_compact_carrier K) (d/2)).
have hZOpen:@open XT Z.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY
    U W F hRestricted hWOpen).
exists Z;split.
- move=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX Z x).2
    (open_nbhs_nbhs (conj hZOpen hx)).
split.
- move=>x hx;split;first exact:(smooth_compact_in_domain K x hx).
  apply:(@metric_open_thickening_includes R YT
    (F @` smooth_compact_carrier K) (d/2) hHalf).
  by exists x.
split;first by move=>x hx;exact:hx.1.
split.
- move=>hEmpty;apply/seteqP;split;last by move=>x hx.
  move=>x [_ [y [z hz hZy] hNear]].
  by move:hz;rewrite hEmpty.
- have[N hN]:=hUniform (d/2) hHalf.
  exists N=>i hi x [_ [y hy hNear]].
  apply:hTube;exists y;first exact:hy.
  have hError:mdist (F x:YT) (a i x:YT)<d/2.
    change (is_true (NY (F x-a i x)<d/2)).
    rewrite (real_seminorm_subtract hNY.1).
    exact:(@hN i hi x).
  have hTriangle:=metric_triangle y (F x:YT) (a i x:YT).
  change (is_true (mdist y (F x:YT)<d/2)) in hNear.
  have hSum:mdist y (F x:YT)+mdist (F x:YT) (a i x:YT)<d by lra.
  exact:(le_lt_trans hTriangle hSum).
Qed.
