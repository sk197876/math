(** Federer (1969), 4.1.1, p. 344: the
    corrected nonembedding assertion distinguishes the zero-
    dimensional source. A nonzero real normed source
    has no nonempty compact open subset, by the
    connectedness and compact bounds already proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormClassZeroWhole
  NormCompactFunctionBound NormSpaceConnected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_norm_nonzero_noncompact]: a nonzero
    real normed vector space is not compact,
    supporting the corrected source exception in
    Federer 4.1.1, p. 344. *)
Theorem real_norm_nonzero_noncompact (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N):
  (exists y:X,y<>0) ->~compact (@setT (real_norm_metric_space hN)).
Proof.
move=>[y hy] hCompact.
have hIdCont:continuous (fun x:real_norm_metric_space hN=>x).
  by move=>x; exact:cvg_id.
have hId:=@norm_continuous_whole_class_zero R X X N N hN hN (fun x=>x) hIdCont.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X N N hN hN setT setT (fun x=>x)
  hCompact (fun _ _=>Logic.I) hId.
have hyPos:0<N y.
  rewrite (real_norm_positive hN.1 hN.2); apply/eqP; exact hy.
have hyNe:N y!=0 by rewrite (gt_eqF hyPos).
have hc:0<(M+1)/N y by rewrite divr_gt0 //; lra.
have hValue:N (((M+1)/N y)*:y)=M+1.
  by rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW hc)) divfK.
have hBad:=hBound (((M+1)/N y)*:y) Logic.I.
rewrite hValue in hBad.
clear -hBad; lra.
Qed.

(** Source for [real_norm_nonempty_open_noncompact]: every
    nonempty open subset of a nonzero real normed
    source is noncompact, supporting the positive-
    dimensional correction of Federer 4.1.1,
    p. 344. No finite basis is needed
    for this supporting topological fact. *)
Theorem real_norm_nonempty_open_noncompact (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (U:set (real_norm_metric_space hN)):
  (exists y:X,y<>0) ->open U ->U !=set0 ->~compact U.
Proof.
move=>hNonzero hOpen hNonempty hCompact.
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hN)) hCompact.
have hConn:=@real_norm_space_connected R X N hN.
have hWhole:U=setT.
  apply:(hConn U hNonempty).
  - exists U; first exact hOpen; by rewrite setTI.
  - exists U; first exact hClosed; by rewrite setTI.
apply:(@real_norm_nonzero_noncompact R X N hN hNonzero).
by rewrite -hWhole.
Qed.
