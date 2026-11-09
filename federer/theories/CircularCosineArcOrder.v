(** Federer (1969), 3.3.19, p. 305: cosine order
    identifies the actual angular interval of a circular cap. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularCosineReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Order.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).

(** Source for [circular_cosine_arc_order]: for the actual
    principal signed angle d in [-pi,pi], the original cap
    inequality cos(gamma)<=cos(d) is equivalent to
    |d|<=gamma, supporting 3.3.19, p. 305.
    Both zero and full half-angle endpoints are retained. *)
Theorem circular_cosine_arc_order (d gamma:R):
  -p<=d ->d<=p ->0<=gamma ->gamma<=p ->
  (C gamma<=C d <->`|d|<=gamma).
Proof.
move=>hdLower hdUpper hGamma hGammaP.
have hAbs:0<=`|d| := normr_ge0 d.
have hAbsP:`|d|<=p by rewrite ler_norml;apply/andP;by split.
have hCosAbs:C `|d|= C d.
  case:(leP 0 d)=>hd0.
  - by rewrite ger0_norm.
  - by rewrite (ltr0_norm hd0) (circular_trig_cosine_even ht).
split.
- move=>hCos;case:(leP `|d| gamma)=>// hNotInside.
  have hStrict:= @circular_trig_cosine_decreases R S C (@CircularTrigonometry.arcsine R)
    (@CircularTrigonometry.arccosine R) p ht gamma `|d| hGamma hGammaP hAbs hAbsP hNotInside.
  rewrite hCosAbs in hStrict;exfalso.
  have hFalse:= le_lt_trans hCos hStrict;by rewrite ltxx in hFalse.
- move=>hInside;rewrite -hCosAbs.
  exact:(@circular_cosine_weak_decrease R `|d| gamma hAbs hInside hGammaP).
Qed.
End Order.
