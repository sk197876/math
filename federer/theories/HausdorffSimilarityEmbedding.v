(** Federer (1969), 3.2.48, p. 284: a fibre
    parametrization magnifying distances by sqrt(2) multiplies
    its q-dimensional Hausdorff measure by sqrt(2)^q.
    Supporting general positive-similarity image law, from the
    two actual-domain Lipschitz bounds of 2.10.11, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import LipschitzUP HausdorffMeasure HausdorffRestrictedLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_similarity_embedding_invariance]: supporting
    the first fibre-integral equality in 3.2.48, p. 284.
    Only an actual left inverse is needed. The reverse
    bound is used solely on the actual image; arbitrary
    original subsets, infinite mass and degree zero remain. *)
Theorem hausdorff_similarity_embedding_invariance (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X) (c:R):
  (0<c)%R ->cancel f g ->(forall x y,mdist (f x) (f y)=(c*mdist x y)%R) ->
  forall q A,@hausdorff_measure R Y q (f @` A)=
    (c^+q)%R%:E*@hausdorff_measure R X q A.
Proof.
move=>hc hLeft hDistance q A.
have hc0:c!=0%R by rewrite gt_eqF.
have hf:is_metric_lipschitz_bound A f c.
  split; first exact:ltW hc.
  by move=>x y _ _; rewrite hDistance.
have hg:is_metric_lipschitz_bound (f @` A) g c^-1.
  split; first by rewrite invr_ge0; exact:ltW hc.
  move=>x y [u hu <-] [v hv <-]; rewrite !hLeft hDistance.
  by rewrite mulrA mulVf // mul1r.
have hUpper:=@hausdorff_lipschitz_on_bound R X Y A f c q A hf (fun x hx=>hx).
have hLower:=@hausdorff_lipschitz_on_bound R Y X (f @` A) g c^-1 q (f @` A) hg (fun y hy=>hy).
have hImage:g @` (f @` A)=A.
  apply/seteqP; split=>x.
  - by move=>[y [z hz <-] <-]; rewrite hLeft.
  - move=>hx; exists (f x); last exact:hLeft.
    by exists x.
rewrite hImage in hLower.
have hPower:(0<=(c^+q)%R%:E)%E by rewrite lee_fin; exact:exprn_ge0 (ltW hc).
have hScaled:=lee_wpmul2l hPower hLower.
have hCancel:((c^+q)*(c^-1)^+q= 1)%R.
  by rewrite -exprMn mulfV // expr1n.
rewrite muleA -EFinM hCancel mul1e in hScaled.
by apply/eqP; rewrite eq_le hUpper hScaled.
Qed.
