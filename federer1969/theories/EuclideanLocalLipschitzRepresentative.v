(** Federer (1969), 4.1.2, p. 347: a locally Lipschitz
    input agrees on every closed source ball with an actual globally
    Lipschitz field. The existing nonexpanding Euclidean retraction
    avoids any extension premise on the Banach target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness FiniteCoordinates FiniteNormMetricCompactness MetricClosedBalls
  LipschitzUP NormLocalLipschitzCompact EuclideanClosedBallRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_local_lipschitz_representative_exists]:
    the compact localization of the locally Lipschitz input in
    Federer 4.1.2, p. 347. The representative agrees at every
    point of the prescribed ball, including its boundary. *)
Theorem euclidean_local_lipschitz_representative_exists (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R n->Y):
  is_locally_metric_lipschitz setT
    (f:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))
      ->real_norm_metric_space hNY) ->
  forall r:R,0<=r ->exists g:R_n R n->Y,exists L:R,0<L /\
    (forall x y,NY (g x-g y)<=L*inner_norm (@euclidean_inner_productP R n) (x-y)) /\
    (forall x,inner_norm (@euclidean_inner_productP R n) x<=r ->g x=f x).
Proof.
move=>hLocal r hr.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose K:set (real_norm_metric_space hN):=[set x|N x<=r].
have hK:compact K:=@finite_norm_metric_ball_compact R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) r.
have[L [hL hLip]]:=@norm_local_lipschitz_compact R X Y N NY hN hNY f K hLocal hK.
have[P [hMember [hFixed hContract]]]:=@euclidean_closed_ball_retraction_exists R n 0 r hr.
have hPM x:N (P x)<=r.
  have h:=hMember x; change (is_true (inner_norm (@euclidean_inner_productP R n) (0-P x)<=r)) in h.
  by rewrite sub0r inner_normN in h.
have hPI x:N x<=r ->P x=x.
  move=>hx; apply:hFixed.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (0-x)<=r)).
  by rewrite sub0r inner_normN.
have hPC x y:N (P x-P y)<=N (x-y).
  have h:=hContract.2 x y Logic.I Logic.I.
  change (is_true (N (P x-P y)<=1*N (x-y))) in h.
  by rewrite mul1r in h.
exists (fun x=>f (P x)),L; split; first exact hL.
split.
- move=>x y; exact:le_trans (hLip.2 (P x) (P y) (hPM x) (hPM y))
    (ler_wpM2l (ltW hL) (hPC x y)).
- by move=>x hx; rewrite (hPI x hx).
Qed.
