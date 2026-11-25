(** Federer (1969), 3.2.33, p. 270: the primitive
    is strictly increasing because its nonnegative derivative
    is positive on a dense union of intervals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals DenseSmallIntervalFamilyUP
  RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_positive_primitive_strictly_increasing]:
    g is increasing in Federer 3.2.33, p. 270,
    in the strict sense needed for the printed fibre cubes.
    A constant increment would make g constant throughout
    that interval by monotonicity. Its actual derivative there
    would vanish, contradicting a dense positive-derivative point.
    No strict monotonicity or injectivity is assumed. *)
Theorem dense_positive_primitive_strictly_increasing (R:realType)
    (a b:nat->R) (psi g:R->R):
  is_dense_small_interval_family a b ->
  (forall t,0<psi t <->(\bigcup_j real_open_interval (a j) (b j)) t) ->
  (forall x,real_open_interval 0 1 x ->has_real_curve_derivative g x (psi x)) ->
  (forall u v:R,0<=u ->u<=v ->v<= 1 ->0<=g v-g u) ->
  forall u v:R,real_open_interval 0 1 u ->real_open_interval 0 1 v ->u<v ->g u<g v.
Proof.
move=>hFamily hPositive hDerivative hMono u v [hu0 hu1] [hv0 hv1] huv.
have hGU: g u<=g v by have:=hMono u v (ltW hu0) (ltW huv) (ltW hv1); rewrite subr_ge0.
case:(ltP (g u) (g v))=>hStrict; first by [].
have hEqual:g u= g v by apply/eqP; rewrite eq_le hGU hStrict.
have hOpen:open (real_open_interval u v):=@real_open_interval_open R u v.
have hNonempty:exists x,real_open_interval 0 1 x /\real_open_interval u v x.
  have [hLeft hRight]:=midf_lt huv.
  exists ((u+v)/2); split; split; lra.
have [x [[hux hxv] hVx]]:=dense_small_interval_hits hFamily hOpen hNonempty.
have hxT:real_open_interval 0 1 x by split; lra.
have hxPositive:0<psi x:=(hPositive x).2 hVx.
have hConstant t:u<=t ->t<=v ->g t= g u.
  move=>hut htv.
  have ht0:0<=t by lra.
  have ht1:t<= 1 by lra.
  have hLow: g u<=g t by have:=hMono u t (ltW hu0) hut ht1; rewrite subr_ge0.
  have hHigh: g t<=g v by have:=hMono t v ht0 htv (ltW hv1); rewrite subr_ge0.
  apply/eqP; rewrite eq_le hLow andbT; by rewrite hEqual.
have hZero:has_real_curve_derivative g x 0.
  move=>e he.
  pose r:R:=Order.min (x-u) (v-x).
  have hr:0<r by rewrite /r lt_min !subr_gt0 hux hxv.
  exists r; split; first exact hr.
  move=>h /andP [hNonzero hSmall].
  have hBounds: -r<h<r by rewrite -ltr_norml.
  have /andP [hLeft hRight]:=hBounds.
  have hru:r<=x-u by rewrite /r ge_min lexx.
  have hrv:r<=v-x by rewrite /r ge_min lexx orbT.
  have hX: g x= g u:=hConstant x (ltW hux) (ltW hxv).
  have hXH:g (x+h)= g u by apply:hConstant; lra.
  by rewrite hXH hX subrr mul0r subr0 normr0.
have hUnique:=@punctured_real_limit_unique R (fun h=>(g (x+h)-g x)/h) (psi x) 0
  (hDerivative x hxT) hZero.
by rewrite hUnique ltxx in hxPositive.
Qed.
