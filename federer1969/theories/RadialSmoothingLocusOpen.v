(** Federer (1969), 4.1.15, p. 372: openness of
    the literal radial agreement locus, and of its
    original admissible local convolution domain. Closed
    balls are retained; no global extension or target
    image hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormClassZeroTopology
  NormClassZeroWhole NormClassZeroArithmetic InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  OpenLocalLipschitzCompact ClosedBallContainmentOpen RadialSmoothingAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_strict_norm_sublevel_open]: an
    original continuous field's strict norm sublevel is open
    in its open domain. This supports the printed open
    agreement locus in 4.1.15, p. 372. *)
Theorem norm_class_zero_strict_norm_sublevel_open (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (f:X->Y) (r:R):
  norm_class_zero NX NY U f ->
  @open (real_norm_metric_space hNX) [set x|U x /\ NY (f x)<r].
Proof.
move=>hf;rewrite openE=>a [ha hLess].
have hEps:0<r-NY (f a) by lra.
have [d [hd hNear]]:=@norm_class_zero_local_control R X Y NX NY hNX
  U f a (r-NY (f a)) hf ha hEps.
apply:(metricType_numDomainType.nbhs_mdistP (a:real_norm_metric_space hNX) _).2.
exists d;first exact:hd.
move=>b hb.
have hDistance:NX (b-a)<d.
  change (is_true (NX (a-b)<d)) in hb.
  by rewrite (real_seminorm_subtract hNX.1).
have [hUb hChange]:=hNear b hDistance.
split;first exact:hUb.
have hTriangle:=real_seminorm_triangle hNY.1 (f b-f a) (f a).
rewrite subrK in hTriangle;lra.
Qed.

(** Source for [radial_smoothing_agreement_locus_open]: the literal
    Z_(r,epsilon) of 4.1.15, p. 372, is open
    for global continuous representatives. Every real radius
    is permitted by the supporting compact-ball argument. *)
Theorem radial_smoothing_agreement_locus_open (R:realType) n nu
    (U:set (R_n R n)) (f g:R_n R n->R_n R nu) (r epsilon:R):
  @open (real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n))) U ->
  continuous (fun x:real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n))=>(f x:real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R nu)))) ->
  continuous (fun x:real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n))=>(g x:real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R nu)))) ->
  @open (real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n)))
    (radial_smoothing_agreement_locus U f g r epsilon).
Proof.
move=>hU hf hg.
pose X:=R_n R n;pose Y:=R_n R nu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R nu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose O:set X:=[set x|NY (g x-f x)<r].
have hDifference:=norm_class_zero_subtract hNY
  (@norm_continuous_whole_class_zero R X Y NX NY hNX hNY g hg)
  (@norm_continuous_whole_class_zero R X Y NX NY hNX hNY f hf).
have hO:@open (real_norm_metric_space hNX) O.
  have hOpen:=@norm_class_zero_strict_norm_sublevel_open R X Y NX NY hNX hNY
    setT (fun x=>g x-f x) r hDifference.
  change (@open (real_norm_metric_space hNX) (setT `&` O)) in hOpen.
  by rewrite setTI in hOpen.
exact:(@openI (real_norm_metric_space hNX) U
  (norm_closed_ball_containment O epsilon) hU
  (@closed_ball_containment_open R n O epsilon hO)).
Qed.

(** Source for [radial_smoothing_valid_local_locus]: the original
    local convolution domain also requires the closed kernel
    ball to lie in U. This domain convention of
    4.1.2 is retained in the 4.1.15 argument. *)
Definition radial_smoothing_valid_local_locus (R:realType) n nu
    (U:set (R_n R n)) (f g:R_n R n->R_n R nu) (r epsilon:R):set (R_n R n):=
  radial_smoothing_agreement_locus U f g r epsilon `&`
    norm_closed_ball_containment U epsilon.

(** Source for [radial_smoothing_valid_local_locus_open]: the
    printed open-locus assertion of 4.1.15, p. 372,
    on the original admissible local convolution domain,
    for the original locally Lipschitz maps on U. No
    continuity outside U is required. *)
Theorem radial_smoothing_valid_local_locus_open (R:realType) n nu
    (U:set (R_n R n)) (f g:R_n R n->R_n R nu) (r epsilon:R):
  (forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) U x) ->
  @is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f ->
  @is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g ->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (radial_smoothing_valid_local_locus U f g r epsilon).
Proof.
move=>hU hf hg.
pose X:=R_n R n;pose Y:=R_n R nu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R nu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose O:set X:=[set x|U x /\NY (g x-f x)<r].
have hDifference:=norm_class_zero_subtract hNY
  (@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U g hU hg)
  (@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hf).
have hO:@open (real_norm_metric_space hNX) O:=
  @norm_class_zero_strict_norm_sublevel_open R X Y NX NY hNX hNY U
    (fun x=>g x-f x) r hDifference.
have hUOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
have hEqual:radial_smoothing_valid_local_locus U f g r epsilon=
    U `&` norm_closed_ball_containment O epsilon.
  apply:funext=>x;apply:propext;split.
  - move=>[[hx hDiff] hBall];split;first exact:hx.
    move=>y hy;exact:conj (hBall y hy) (hDiff y hy).
  - move=>[hx hBall];split.
    + split;first exact:hx;move=>y hy;exact:(hBall y hy).2.
    + move=>y hy;exact:(hBall y hy).1.
rewrite hEqual.
exact:(@openI (real_norm_metric_space hNX) U
  (norm_closed_ball_containment O epsilon) hUOpen
  (@closed_ball_containment_open R n O epsilon hO)).
Qed.
