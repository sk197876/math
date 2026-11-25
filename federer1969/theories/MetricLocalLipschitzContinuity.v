(** Federer (1969), 4.1.2, p. 347: locally Lipschitz
    inputs are continuous for their original norm metrics.
    This supporting metric proof uses only the local distance bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_local_lipschitz_continuous_whole]: the
    continuity implicit in the locally Lipschitz input clause
    of Federer 4.1.2, p. 347, on the original whole source. *)
Theorem metric_local_lipschitz_continuous_whole (R:realType) (X Y:metricType R)
    (f:X->Y):
  is_locally_metric_lipschitz setT f ->continuous f.
Proof.
move=>hLocal x W hW.
have[V [hV [L [hL hBound]]]]:=hLocal x Logic.I.
have[r hr hBallV]:=(metricType_numDomainType.nbhs_mdistP x V).1 hV.
have[eta hEta hBallW]:=(metricType_numDomainType.nbhs_mdistP (f x) W).1 hW.
have hVx:V x:=nbhs_singleton hV.
have hRadius:0<Num.min r (eta/L) by rewrite lt_min hr divr_gt0.
apply:(filterS _ (nbhsx_ballx x (Num.min r (eta/L)) hRadius)).
move=>y hy.
have hNear:mdist x y<Num.min r (eta/L) by move:hy; rewrite ballEmdist.
move:hNear; rewrite lt_min=>/andP[hyr hyEta].
apply:hBallW.
have hDist:=hBound.2 x y (conj Logic.I hVx) (conj Logic.I (hBallV y hyr)).
apply:le_lt_trans hDist _.
by rewrite mulrC -ltr_pdivlMr.
Qed.
