(** Federer (1969), 3.2.26(2), p. 261: small
    normalized secants of a compact rectifiable chart lie
    in every open neighbourhood of its unit tangent disc.
    Expand the printed thin-tube containment using the actual
    differential and the inverse Lipschitz estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP NormDifferentialUP OrthogonalMaps MetricClosedBalls
  MetricOpenThickening MetricCompactNeighbourhood OrthogonalDiscGeometricGauge NormUnitDiscApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [differentiable_chart_unit_disc_neighbourhood]: the
    containment W intersect B(w,r) in C(w,r) in
    3.2.26(2), p. 261. The erratum p. 5,
    book p. 261 line 29, corrects the displacement
    to x-w. The quantitative differentiability estimate puts
    (psi(b)-psi(a))/r within an arbitrarily small distance
    of the unit disc of the actual differential image.
    The open neighbourhood may depend on that image. *)
Theorem differentiable_chart_unit_disc_neighbourhood (R:realType) m n
    (K:set (R_n R m)) (psi:R_n R m->R_n R n) a
    (D:Hom (R_n R m) (R_n R n)) (f:{linear R_n R m->R_n R n}) (lambda:R)
    (U:set (inner_metric_space (@euclidean_inner_productP R n))):
  0<lambda ->
  (forall b,K b ->inner_norm (@euclidean_inner_productP R m) (b-a)<=
    lambda*inner_norm (@euclidean_inner_productP R n) (psi b-psi a)) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a D ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) f ->
  (forall x,exists u,f u=D x) ->open U ->
  f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0:R_n R m) 1) `<=` U ->
  exists s:R,0<s /\forall r:R,0<r<s ->forall b,K b ->
    inner_norm (@euclidean_inner_productP R n) (psi b-psi a)<=r ->
    U (r^-1*:(psi b-psi a)).
Proof.
move=>hLambda hInverse hD hF hRange hOpen hDisc.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose B:=f @` (@metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R m)) (0:R_n R m) 1).
have [rho [hRho hThick]]:=@compact_metric_open_thickening R
  (inner_metric_space (@euclidean_inner_productP R n)) B U
  (orthogonal_unit_disc_compact hF) hOpen hDisc.
pose e:R:=rho/4.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have hEpsilon:0<e/lambda by rewrite divr_gt0.
have [s [hs hRemainder]]:=norm_differential_remainder hD hEpsilon.
exists (s/lambda); split; first by rewrite divr_gt0.
move=>r /andP [hr hrs] b hb hDistance.
have hParameter:NX (b-a)<s.
  apply:le_lt_trans (hInverse b hb) _.
  apply:le_lt_trans (ler_wpM2l (ltW hLambda) hDistance) _.
  move:hrs; by rewrite ltr_pdivlMr // mulrC.
have hApprox:=hRemainder (b-a) I hParameter.
have hShift:a+(b-a)=b by rewrite addrC subrK.
rewrite hShift in hApprox.
pose v:=r^-1*:(psi b-psi a).
pose y:=r^-1*:D (b-a).
have hRinv:0<=r^-1 by rewrite invr_ge0; exact:ltW hr.
have hRnonzero:r!=0 by rewrite gt_eqF.
have hLambdaNonzero:lambda!=0 by rewrite gt_eqF.
have hV:NY v<=1.
  rewrite /v /NY inner_normZ (ger0_norm hRinv).
  have h:=ler_wpM2l hRinv hDistance; by rewrite mulVf in h.
have hError:NY (v-y)<=e.
  rewrite /v /y /NY -scalerBr inner_normZ (ger0_norm hRinv).
  apply:le_trans (ler_wpM2l hRinv hApprox) _.
  have hMass:=hInverse b hb.
  have hParam:NX (b-a)<=lambda*r:=le_trans hMass (ler_wpM2l (ltW hLambda) hDistance).
  have hEpsNonnegative:0<=e/lambda:=ltW hEpsilon.
  apply:le_trans (ler_wpM2l hRinv (ler_wpM2l hEpsNonnegative hParam)) _.
  have hCancel:r^-1*((e/lambda)*(lambda*r))=e.
    by rewrite [(e/lambda)*(lambda*r)]mulrA (divfK hLambdaNonzero)
      mulrCA (mulVf hRnonzero) mulr1.
  by rewrite hCancel.
have [hZ hNear]:=@norm_near_unit_rescaling R (R_n R n) NY
  (inner_norm_real_norm (@euclidean_inner_productP R n)) v y e (ltW he) hV hError.
pose z:=(1+e)^-1*:y.
have [u hu]:=hRange (r^-1*:(b-a)).
have hY:f u=y by rewrite hu linearZ.
have hZB:B z.
  exists ((1+e)^-1*:u); last by rewrite linearZ hY.
  change (is_true (@mdist R (inner_metric_space (@euclidean_inner_productP R m)) (0:R_n R m) ((1+e)^-1*:u)<=1)).
  rewrite inner_metric_distanceE sub0r inner_normN.
  rewrite -(orthogonal_map_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) hF) linearZ hY.
  exact hZ.
apply:(hThick v); exists z; first exact hZB.
change (is_true (@mdist R (inner_metric_space (@euclidean_inner_productP R n)) z v<rho)).
rewrite inner_metric_distanceE -[z-v]opprB inner_normN.
apply:le_lt_trans hNear _; rewrite /e; lra.
Qed.
