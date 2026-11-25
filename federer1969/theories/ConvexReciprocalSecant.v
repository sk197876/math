(** Federer 3.2.45, p. 279: a valid consequence of the
    stated convexity and monotonicity. The denominator v is
    essential. This estimate gives a local finite-exponent modulus;
    it does not supply continuity at reciprocal exponent zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology lra ring.
From Federer Require Import ConvexFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_nonincreasing_reciprocal_secant]: corrected
    supporting convex-function step for Federer 3.2.45, p. 279.
    If h is convex and nonincreasing on [0,1] and h(0)-h(1)<=C,
    then 0<=h(u)-h(v)<=C(v-u)/v for 0<=u<v<=1. This
    records the actual implication and retains the endpoint u=0;
    a separate argument is needed for uniform continuity there. *)
Theorem convex_nonincreasing_reciprocal_secant (R:realType) (h:R^o->R) (C:R):
  is_real_convex_function_on [set x:R^o|0<=x<=1] h ->
  (forall x y:R,0<=x ->x<=y ->y<=1 ->h y<=h x) ->
  h 0-h 1<=C ->forall u v:R,0<=u ->u<v ->v<=1 ->
  0<=h u-h v /\h u-h v<=C*(v-u)/v.
Proof.
move=> [hDomain hConvex] hMono hRange u v hu huv hv1.
have hv:0<v:=le_lt_trans hu huv.
have hvNe:v!=0:=lt0r_neq0 hv.
have hVC:[set x:R^o|0<=x<=1] v by rewrite /= (ltW hv) hv1.
have h0C:[set x:R^o|0<=x<=1] 0 by rewrite /= ler01 lexx.
have hQ:0<=u/v:=divr_ge0 hu (ltW hv).
have hQ1:u/v<=1 by rewrite ler_pdivrMr // mul1r;exact:ltW huv.
have hCombination:((1-u/v)*:(0:R^o)+(u/v)*:(v:R^o))=u.
  change ((1-u/v)*0+(u/v)*v=u);by rewrite mulr0 add0r divfK.
have hChord:=hConvex 0 v h0C hVC (u/v) hQ hQ1.
rewrite hCombination in hChord.
have hIdentity:(1-u/v)*h 0+(u/v)*h v=h v+(1-u/v)*(h 0-h v) by ring.
rewrite hIdentity in hChord.
have hStep:h u-h v<=(1-u/v)*(h 0-h v).
  by rewrite lerBlDl.
have hEnd:h 1<=h v:=hMono v 1 (ltW hv) hv1 (lexx 1).
have hRangeV:h 0-h v<=C by lra.
have hNonnegative:0<=1-u/v by rewrite subr_ge0.
have hBound:=ler_wpM2l hNonnegative hRangeV.
have hFinal:(1-u/v)*C=C*(v-u)/v by field;by rewrite hvNe.
rewrite hFinal in hBound.
split.
- rewrite subr_ge0;exact:hMono u v hu (ltW huv) hv1.
- exact:le_trans hStep hBound.
Qed.
