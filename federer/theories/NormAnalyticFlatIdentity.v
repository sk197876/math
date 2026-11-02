(** Federer (1969), 3.1.24, p. 240: connectedness
    makes the relatively clopen flat-point set either empty or
    the entire analytic domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormAnalyticUP NormAnalyticLocal NormSmoothFields NormAnalyticZeroJetSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_flat_identity]: the clopen-set
    inference W=A or W empty in Federer 3.1.24, p. 240.
    On a connected domain, an analytic map with every
    differential zero at one point is identically zero. This
    implication holds for arbitrary normed source and target
    spaces without a completeness hypothesis. *)
Theorem norm_analytic_flat_identity (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X Y NX NY hNX hNY A f -> A a ->
  (forall m (z:@ContinuousMultilinear.space R m X Y NX NY hNX hNY),
    has_norm_higher_differential NX
      (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
      (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f m a z -> z=0) ->
  forall x,A x -> f x=0.
Proof.
move=>hconn hf ha hflat.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
have [D hD]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY A f (norm_analytic_class_all_orders hf).
pose W:=norm_zero_jet_set A D.
have hWa:W a.
  split; first exact ha.
  move=>m; exact (hflat m (D m a) ((hD m).1 a ha)).
have hWnon:W!=set0 by exists a.
have hWopen:=@norm_analytic_zero_jets_open R X Y NX NY hNX hNY A f D hf
  (fun i=>(hD i).1) (fun i=>(hD i).2).
have hWrel:exists2 C:set (real_norm_metric_space hNX),open C & W=A `&` C.
  exists W; first exact hWopen.
  apply/seteqP; split=>x hx; first by split; [exact hx.1|exact hx].
  exact hx.2.
have hWclosed:=@norm_analytic_zero_jets_relative_closed R X Y NX NY hNX hNY A D
  (fun i=>(hD i).2).
have hWA:W=A:=hconn W hWnon hWrel hWclosed.
move=>x hx.
have hxW:W x by rewrite hWA.
have hh:=((hD 0%N).1 x hx).2.
rewrite hxW.2 linear0 in hh; exact (esym hh).
Qed.
