(** Federer (1969), 3.4.8(11), p. 333:
    an interior maximum belongs to the
    actual critical set. This supporting
    Fermat argument uses the project's proved
    directional difference-quotient limit from 3.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_local_maximum_zero]:
    the interior maximum of Psi is
    critical, 3.4.8(11), p. 333.
    This holds in an arbitrary normed
    source, without completeness or finite dimension. *)
Theorem norm_differential_local_maximum_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (f:X->R^o) a (L:Hom X R^o):
  has_norm_differential NX (fun z:R^o=>`|z|) A f a L ->
  (exists r:R,0<r /\ forall h,NX h<r ->f (a+h)<=f a) ->
  forall v,L v = 0.
Proof.
move=>hL [r [hr hMaximum]].
have hNonpositive v:L v<=0.
  case:(leP (L v) 0)=>// hPositive.
  have hE:0<L v/2 by rewrite divr_gt0 // ltr0n.
  have [d [hd hLimit]]:=@norm_differential_directional_limit R X R^o NX
    (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f a L hL v (L v/2) hE.
  have hNorm:0<NX v+1 by have:=real_seminorm_nonnegative hNX.1 v;lra.
  pose c:=Num.min d (r/(NX v+1)).
  have hc:0<c by rewrite /c lt_min hd divr_gt0.
  pose t:=c/2.
  have ht:0<t by rewrite /t divr_gt0 // ltr0n.
  have htc:t<c by rewrite /t;lra.
  have hcd:c<=d by rewrite /c ge_min lexx.
  have hcr:c<=r/(NX v+1) by rewrite /c ge_min lexx orbT.
  have htd:t<d:=lt_le_trans htc hcd.
  have htr:t<r/(NX v+1):=lt_le_trans htc hcr.
  have hProduct:t*(NX v+1)<r by move:htr;rewrite ltr_pdivlMr.
  have hSmall:NX (t*:v)<r.
    rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
    have hNV:=real_seminorm_nonnegative hNX.1 v;nra.
  have hValue:=hMaximum (t*:v) hSmall.
  have hQuot:t^-1*(f (a+t*:v)-f a)<=0.
    apply:mulr_ge0_le0;first by rewrite invr_ge0;exact:ltW ht.
    by rewrite subr_le0.
  have hAbs:`|t| = t:=ger0_norm (ltW ht).
  have hBoth:(0<`|t|) && (`|t|<d) by rewrite hAbs ht htd.
  have hError:=hLimit t hBoth.
  change (is_true (`|t^-1*(f (a+t*:v)-f a)-L v|<L v/2)) in hError.
  have hDiff:t^-1*(f (a+t*:v)-f a)-L v<=0 by lra.
  rewrite (ler0_norm hDiff) in hError;by lra.
move=>v;have hV:=hNonpositive v;have hMinus:=hNonpositive (-v).
rewrite linearN /= in hMinus.
apply/eqP;rewrite eq_le hV;by lra.
Qed.
