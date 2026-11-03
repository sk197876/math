(** Federer (1969), 3.2.43, printed p. 278:
    supporting geometric fact for placing the two strips
    in the boundary tube. A nearest point to an exterior
    point cannot be an interior point of the source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormSmallStrictContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_nearest_outside_not_interior]: supporting
    boundary-tube inclusion in Federer 3.2.43, p. 278.
    Independent norm and nearest-point laws suffice. Moving
    a small distance towards the original exterior point
    would strictly decrease its positive nearest distance,
    contradicting minimality. No convexity is assumed. *)
Lemma norm_nearest_outside_not_interior (R:realType) (V:lmodType R)
    (N:V->R) (C:set V) (x a:V):
  is_real_norm N ->C a ->~C x ->
  (forall z,C z ->N (x-a)<=N (x-z)) ->
  ~norm_domain_interior N C a.
Proof.
move=>hN ha hx hMinimum [d [hd hInside]].
pose v:=x-a.
have hVNe:v!=0.
  apply/eqP=>hZero.
  have hEqual:x=a by apply/eqP; by rewrite -subr_eq0 -/v hZero.
  apply:hx; by rewrite hEqual.
have hVPositive:0<N v by rewrite (@real_norm_positive R V N hN.1 hN.2 v).
have [t [ht0 [ht1 hNear]]]:=norm_small_strict_contraction hN v hd.
have hSmall:N (v-t*:v)<d.
  by rewrite -[v-t*:v]opprB (real_seminorm_negate hN.1).
have hPoint:C (a+(v-t*:v)):=hInside (v-t*:v) hSmall.
have hPointEq:a+(v-t*:v)=x-t*:v.
  by rewrite addrA /v [a+(x-a)]addrC subrK.
have hDifference:x-(a+(v-t*:v))=t*:v.
  by rewrite hPointEq opprB addrCA subrr addr0.
have hMinimal:=hMinimum _ hPoint.
rewrite hDifference (real_seminorm_scale hN.1) (ger0_norm (ltW ht0)) in hMinimal.
have hStrict:t*N v<N v.
  by rewrite -[X in _<X]mul1r ltr_pM2r.
have hBad:=le_lt_trans hMinimal hStrict.
by rewrite ltxx in hBad.
Qed.
