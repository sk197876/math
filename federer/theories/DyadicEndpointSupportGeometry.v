(** Federer (1969), 4.1.12, p. 368: the
    endpoints of the first interval series, with
    their limit zero, form the compact set
    {0} union {2^(-k):k>=1}. Every nonzero
    point is isolated. Reuse the earlier closedness
    theorem for shrinking finite metric layers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality reals topology normedtype lra.
From Federer Require Import RealMetricBackground GeometricUniformTail ShrinkingFiniteMetricLayersClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dyadic_endpoint_point]: the original
    endpoints 2^(-(k+1)), jointly enumerating the
    two endpoint families in Federer 4.1.12, p. 368. *)
Definition dyadic_endpoint_point (R:realType) k:R:=(1/2)^+k.+1.

(** Source for [dyadic_endpoint_set]: the original
    endpoint set together with its accumulation point,
    supporting the support assertion of Federer
    4.1.12, p. 368. *)
Definition dyadic_endpoint_set (R:realType):set R:=
  [set 0] `|` \bigcup_k [set dyadic_endpoint_point R k].
Arguments dyadic_endpoint_set (R): clear implicits.

(** Source for [dyadic_endpoint_positive]: every
    original endpoint is positive, supporting
    Federer 4.1.12, p. 368. *)
Lemma dyadic_endpoint_positive (R:realType) k:0<dyadic_endpoint_point R k.
Proof.
rewrite /dyadic_endpoint_point;apply:exprn_gt0;by rewrite divr_gt0 // ltr0n.
Qed.

(** Source for [dyadic_endpoint_next]: consecutive
    original endpoints differ by the factor 1/2,
    supporting Federer 4.1.12, p. 368. *)
Lemma dyadic_endpoint_next (R:realType) k:
  dyadic_endpoint_point R k.+1=dyadic_endpoint_point R k/2.
Proof. by rewrite /dyadic_endpoint_point exprSr !mul1r. Qed.

(** Source for [dyadic_endpoint_antitone]: the
    original endpoint sequence is decreasing, supporting
    its support geometry in Federer 4.1.12, p. 368. *)
Lemma dyadic_endpoint_antitone (R:realType) i j:(i<=j)%N->
  dyadic_endpoint_point R j<=dyadic_endpoint_point R i.
Proof.
move=>hij.
have hq0:0<=(1/2:R) by lra.
have hq1:(1/2:R)<=1 by lra.
have hIndex:(i.+1<=j.+1)%N:=hij.
rewrite /dyadic_endpoint_point -(subnKC hIndex) exprD.
have h:=ler_wpM2l (exprn_ge0 i.+1 hq0) (exprn_ile1 (j.+1-i.+1)%N hq0 hq1).
by rewrite mulr1 in h.
Qed.

(** Source for [dyadic_endpoint_set_closed]: the
    actual endpoint set with zero is closed,
    supporting Federer 4.1.12, p. 368.
    No larger closure hull replaces the printed set. *)
Lemma dyadic_endpoint_set_closed (R:realType):@closed (real_line_metric R) (dyadic_endpoint_set R).
Proof.
apply:(@shrinking_finite_metric_layers_closed R (real_line_metric R) 0
  (fun k=>[set dyadic_endpoint_point R k]) (fun _=>finite_set1 _)).
move=>epsilon hEpsilon.
have hq:0<(1/2:R)<1 by apply/andP;split;lra.
have[k hk]:=@geometric_uniform_tail R (1/2) (1/2) epsilon hq (ltW (andP hq).1) hEpsilon.
exists k=>j hkj y ->.
rewrite real_line_metric_distanceE sub0r normrN (ger0_norm (ltW (dyadic_endpoint_positive R j)))
  /dyadic_endpoint_point exprSr.
exact:hk j hkj.
Qed.

(** Source for [dyadic_endpoint_set_compact]: the
    actual original endpoint set is compact inside
    [0,1/2], supporting Federer 4.1.12, p. 368. *)
Lemma dyadic_endpoint_set_compact (R:realType):@compact (real_line_metric R) (dyadic_endpoint_set R).
Proof.
have hC:@compact (real_line_metric R) (`[0,1/2]:set (real_line_metric R)):=@segment_compact R 0 (1/2).
refine (@subclosed_compact (real_line_metric R) (dyadic_endpoint_set R) (`[0,1/2])
  (@dyadic_endpoint_set_closed R) hC _).
move=>y [->|[k _ ->]];rewrite /mkset in_itv /=.
- by rewrite lexx;have h:(0:R)<=1/2 by lra.
- apply/andP;split;first exact:ltW (dyadic_endpoint_positive R k).
  have h:=@dyadic_endpoint_antitone R 0%N k (leq0n k).
  by rewrite /dyadic_endpoint_point expr1 in h.
Qed.

Arguments dyadic_endpoint_set_compact (R): clear implicits.

(** Source for [dyadic_endpoint_set_isolated]: every
    nonzero original endpoint is isolated in the
    full actual set, supporting the normal-current
    support obstruction of Federer 4.1.12, p. 368. *)
Lemma dyadic_endpoint_set_isolated (R:realType) y:
  dyadic_endpoint_set R y->y<>0->exists W:set R,
    @open (real_line_metric R) W /\W y /\
    forall z,dyadic_endpoint_set R z->W z->z=y.
Proof.
move=>[hZero|[k _ hK]] hNonzero;first exact:False_ind _ (hNonzero hZero).
change (y=dyadic_endpoint_point R k) in hK.
subst y.
pose p:=dyadic_endpoint_point R k.
pose W:set (real_line_metric R):=`]((3 * p) / (4 : R)),((3 * p) / (2 : R))[.
have hp:0<p:=dyadic_endpoint_positive R k.
exists W;split;first exact:interval_open.
split.
- change (W p);rewrite /W /mkset in_itv /=;apply/andP;split;lra.
- move=>z [hZero|[j _ hJ]] hWz.
  + rewrite /W /mkset in_itv /= hZero in hWz.
    have hBounds:=andP hWz;exfalso;lra.
  + change (z=dyadic_endpoint_point R j) in hJ.
    subst z.
    have hBounds:(3 * p) / (4 : R)<dyadic_endpoint_point R j<(3 * p) / (2 : R).
      by move:hWz;rewrite /W /mkset in_itv /=.
    have[hLow hHigh]:=andP hBounds.
    case:(ltngtP j k)=>[hjk|hkj|->];last by [].
    * have h:=@dyadic_endpoint_antitone R j.+1 k hjk.
      rewrite dyadic_endpoint_next in h;change (is_true (p<=dyadic_endpoint_point R j / (2 : R))) in h.
      exfalso;lra.
    * have h:=@dyadic_endpoint_antitone R k.+1 j hkj.
      rewrite dyadic_endpoint_next in h;change (is_true (dyadic_endpoint_point R j<=p / (2 : R))) in h.
      exfalso;lra.
Qed.
