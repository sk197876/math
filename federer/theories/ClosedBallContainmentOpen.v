(** Federer (1969), 4.1.15, p. 372: the literal
    closed-ball smoothing agreement locus is open. The
    supporting Euclidean fact is that all translates of
    one compact closed ball contained in an open set
    remain contained for nearby centres. Empty balls and
    dimension zero are included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology ring.
From Federer Require Import RealNormUP NormMetric InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  MetricClosedBalls EuclideanNormClosedBalls MetricOpenThickening
  MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_closed_ball_containment]: the closed
    ball convention in the printed Z_(r,epsilon), Federer
    4.1.15, p. 372. No positive radius is required
    for the elementary openness fact below. *)
Definition norm_closed_ball_containment (R:realType) n
    (O:set (R_n R n)) (epsilon:R):set (R_n R n):=
  [set x|forall y,inner_norm (@euclidean_inner_productP R n) (x-y)<=epsilon->O y].

(** Source for [closed_ball_containment_open]: the closed-ball
    condition defining the original smoothing locus in
    4.1.15, p. 372, is open when O is open.
    Compactness and the earlier uniform open-thickening theorem
    supply one margin for the entire original ball. *)
Theorem closed_ball_containment_open (R:realType) n
    (O:set (R_n R n)) (epsilon:R):
  @open (real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n))) O ->
  @open (real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n))) (norm_closed_ball_containment O epsilon).
Proof.
move=>hO.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT:=real_norm_metric_space hNX.
rewrite openE=>x hx.
pose K:set XT:=metric_closed_ball (x:XT) epsilon.
have hCompact:compact K:=@euclidean_norm_closed_ball_compact R n x epsilon.
have hKO:K `<=` O by move=>y hy;exact:hx y hy.
have [d [hd hTube]]:=@compact_metric_open_thickening R XT K O hCompact hO hKO.
apply:(metricType_numDomainType.nbhs_mdistP (x:XT) _).2.
exists d;first exact:hd.
move=>x' hNear y hy.
pose z:X:=y+(x-x').
have hOld:x-z=x'-y.
  apply/ffunP=>i;rewrite /z !ffunE;ring.
have hDistance:z-y=x-x'.
  apply/ffunP=>i;rewrite /z !ffunE;ring.
apply:hTube.
exists z.
- change (is_true (NX (x-z)<=epsilon));by rewrite hOld.
- change (is_true (NX (z-y)<d));rewrite hDistance;exact:hNear.
Qed.
