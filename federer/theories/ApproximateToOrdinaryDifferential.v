(** Federer (1969), 3.1.5, p. 216: approximate
    differentiability becomes differentiability under uniform local
    Lipschitz control based on a density-one subset. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric
  HilbertFormCompactness RealNormUP NormDifferentialUP NormFiniteLinearBound
  ApproximateDifferentialUP ApproximateDifferentialRemainder
  EuclideanLebesgueDimensions CenteredBallRelations PartialFunctionUP
  MeasureSetDensity MetricClosedBalls EuclideanDensityGoodPoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [linear_remainder_comparison]: the first inequality
    in the proof of Federer 3.1.5, p. 216. Compare the
    remainder at x with that at a nearby good point z, using
    the function increment and the linear increment. *)
Lemma linear_remainder_comparison (R : realType) (X Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (f : X->Y)
    (L : Hom X Y) (a x z : X) :
  NY (f x-f a-L (x-a)) <=
    NY (f z-f a-L (z-a))+NY (f x-f z)+NY (L (x-z)).
Proof.
have hx : x-a=(x-z)+(z-a) by rewrite addrA subrK.
have hf : f x-f a=(f x-f z)+(f z-f a) by rewrite addrA subrK.
rewrite hf hx linearD opprD addrACA.
have h1 := real_seminorm_triangle hNY.1
  (f x-f z-L (x-z)) (f z-f a-L (z-a)).
have h2 := real_seminorm_triangle hNY.1 (f x-f z) (-L (x-z)).
rewrite (real_seminorm_negate hNY.1) in h2.
lra.
Qed.

(** Source for [approximate_to_ordinary_differential]: Federer
    3.1.5, p. 216. The proof uses the printed contained-ball
    selection and the same remainder estimate. A finite bound for L
    replaces its operator norm; this equivalent bound avoids choosing
    an additional norm object. The target may be any normed space. *)
Theorem approximate_to_ordinary_differential (R : realType) n (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (B C : set (R_n R n)) (f : R_n R n->Y)
    (eta M : R) (a : R_n R n) (L : Hom (R_n R n) Y) :
  C `<=` B -> 0<eta -> 0<M ->
  (forall z, C z -> forall x,
    inner_norm (@euclidean_inner_productP R n) (x-z)<eta ->
    B x /\ NY (f x-f z)<=M*inner_norm (@euclidean_inner_productP R n) (x-z)) ->
  C a ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R n)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])
      (~` C)) a 0%E ->
  has_approximate_differential NY B f a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n)) NY B f a L.
Proof.
move=> hCB heta hM hlocal ha hCd hap.
have hminl (x y : R) : Num.min x y<=x by rewrite ge_min lexx.
have hminr (x y : R) : Num.min x y<=y by rewrite ge_min lexx orbT.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose NX := inner_norm (@euclidean_inner_productP R n).
have hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
have hbounded := @norm_finite_linear_bounded R (R_n R n) Y NX NY hNX hNY
  n (@coordinate_basis R n) (@coordinate_basisP R n) L.
have [K [hK hLK]] := hbounded.
constructor.
- exists eta; split=> // h hh.
  have hx : NX ((a+h)-a)<eta by rewrite addrAC subrr add0r.
  exact: (hlocal a ha (a+h) hx).1.
- exact hbounded.
- move=> eps heps.
  pose D := 1+M+K.
  have hD : 0<D by rewrite /D; lra.
  pose e := Num.min (1/2) (eps/(4*D)).
  have he : 0<e.
    rewrite /e lt_min; apply/andP; split.
    + by rewrite divr_gt0 // ltr0n.
    + by rewrite divr_gt0 // mulr_gt0 // ltr0n.
  have hehalf : e<=1/2 := hminl _ _.
  have he1 : e<1 by lra.
  have hden : 0<1-e by lra.
  have hecoef : 4*D*e<=eps.
    have hh : e<=eps/(4*D) := hminr _ _.
    have hp : 0<4*D by rewrite mulr_gt0 // ltr0n.
    have hmul : e*(4*D)<=eps by move: hh; rewrite ler_pdivlMr // mulrC.
    nra.
  have hEd := @approximate_remainder_exceptional_density R n Y NY hNY B f a L e hap he.
  have [d [hd hgood]] := euclidean_zero_density_good_point hCd hEd he.
  pose t := Num.min d eta.
  have ht : 0<t by rewrite /t lt_min hd heta.
  exists ((1-e)*t); split; first by rewrite mulr_gt0.
  move=> h hBh hh.
  have [->|hne] := eqVneq h 0.
    by rewrite addr0 subrr linear0 subr0
      (real_seminorm_zero hNY.1) /NX inner_norm0 mulr0.
  pose u := NX h.
  have hu : 0<u by rewrite /u /NX inner_norm_gt0.
  pose r := u/(1-e).
  have hr : 0<r by rewrite /r divr_gt0.
  have hru : (1-e)*r=u by rewrite /r mulrC mulfVK ?(gt_eqF hden).
  have hrt : r<t.
    rewrite /r ltr_pdivrMr // mulrC; exact hh.
  have hrd : r<d := lt_le_trans hrt (hminl _ _).
  have hreta : r<eta := lt_le_trans hrt (hminr _ _).
  pose x : X := a+h.
  have hax : mdist (a : X) x=u.
    rewrite inner_metric_distanceE /x opprD addrA subrr add0r inner_normN.
    by [].
  have hsub : metric_closed_ball x (e*r) `<=` metric_closed_ball (a : X) r.
    move=> y hy.
    have htri := metric_triangle (a : X) x y.
    change (is_true (mdist (a : X) y<=r)).
    have hb := le_trans htri (lerD (lexx _) hy).
    rewrite hax in hb; nra.
  have [z [hz [hzC hzG]]] := hgood r x hr hrd hsub.
  have hCz : C z := contrapT hzC.
  have hGz : approximate_remainder_good_points NY B f a L e z := contrapT hzG.
  have hzr : NX (z-a)<=r.
    have hb := hsub z hz.
    move: hb; rewrite /metric_closed_ball /= inner_metric_distanceE.
    by rewrite -opprB inner_normN.
  have hxz : NX (x-z)<=e*r.
    exact hz.
  have her : e*r<r by nra.
  have hxeta : NX (x-z)<eta := le_lt_trans hxz (lt_trans her hreta).
  have hfxz := (hlocal z hCz x hxeta).2.
  have hfirst : NY (f z-f a-L (z-a))<=e*r.
    apply: (le_trans (ltW hGz.2.2) _).
    apply: ler_wpM2l; [exact: ltW he|exact hzr].
  have hsecond : NY (f x-f z)<=M*(e*r).
    apply: (le_trans hfxz _).
    apply: ler_wpM2l; [exact: ltW hM|exact hxz].
  have hthird : NY (L (x-z))<=K*(e*r).
    apply: (le_trans (hLK (x-z)) _).
    apply: ler_wpM2l; [exact hK|exact hxz].
  have hb := @linear_remainder_comparison R (R_n R n) Y NY hNY f L a x z.
  have hxha : x-a=h by rewrite /x addrAC subrr add0r.
  rewrite hxha in hb.
  have hbound : NY (f (a+h)-f a-L h)<=D*e*r.
    rewrite /D; change (is_true (NY (f x-f a-L h)<=((1+M)+K)*e*r)); nra.
  have hr2 : r<=2*u by nra.
  have hscale : D*e*r<=D*e*(2*u).
    apply: ler_wpM2l; first exact: mulr_ge0 (ltW hD) (ltW he).
    exact hr2.
  apply: (le_trans hbound (le_trans hscale _)).
  have hc : 2*D*e<=eps by nra.
  have hh' : (2*D*e)*u<=eps*u.
    apply: ler_wpM2r; [exact: ltW hu|exact hc].
  change (is_true (D*e*(2*u)<=eps*u)); nra.
Qed.

(** Source for [federer_3_1_5]: exactly the Euclidean-domain and
    Euclidean-target lemma of Federer 3.1.5, p. 216. The
    same candidate L is the ordinary differential; both definitions
    retain the actual domain B. *)
Corollary federer_3_1_5 (R : realType) m n
    (B C : set (R_n R m)) (f : R_n R m->R_n R n)
    (eta M : R) (a : R_n R m) (L : Hom (R_n R m) (R_n R n)) :
  C `<=` B -> 0<eta -> 0<M ->
  (forall z, C z -> forall x,
    inner_norm (@euclidean_inner_productP R m) (x-z)<eta ->
    B x /\ inner_norm (@euclidean_inner_productP R n) (f x-f z)<=
      M*inner_norm (@euclidean_inner_productP R m) (x-z)) ->
  C a ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R m)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
      (~` C)) a 0%E ->
  has_approximate_differential (inner_norm (@euclidean_inner_productP R n)) B f a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) B f a L.
Proof.
exact (@approximate_to_ordinary_differential R m (R_n R n)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) B C f eta M a L).
Qed.

(** Source for [approximate_to_ordinary_differentiable]: the conclusion
    of Federer 3.1.5, p. 216, phrased as existence of the differential.
    The preceding theorem preserves each supplied approximate differential;
    here its existence suffices. The target is allowed to be any normed
    vector space, a strengthening of the printed Euclidean target. *)
Corollary approximate_to_ordinary_differentiable (R : realType) n (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (B C : set (R_n R n)) (f : R_n R n->Y)
    (eta M : R) (a : R_n R n) :
  C `<=` B -> 0<eta -> 0<M ->
  (forall z, C z -> forall x,
    inner_norm (@euclidean_inner_productP R n) (x-z)<eta ->
    B x /\ NY (f x-f z)<=M*inner_norm (@euclidean_inner_productP R n) (x-z)) ->
  C a ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R n)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])
      (~` C)) a 0%E ->
  approximately_differentiable_at NY B f a ->
  norm_differentiable_at (inner_norm (@euclidean_inner_productP R n)) NY B f a.
Proof.
move=> hCB heta hM hlocal ha hd [L hL]; exists L.
exact: (approximate_to_ordinary_differential hNY hCB heta hM hlocal ha hd hL).
Qed.
