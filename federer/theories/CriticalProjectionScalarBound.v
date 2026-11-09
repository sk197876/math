(** Federer (1969), 3.3.20, p. 307, as corrected
    in the published erratum p. 6, book p. 307 line 26. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_corrected_projection_scalar_bound]:
    the two corrected first-level projected lengths
    are at most 3/sqrt(5), 3.3.20,
    p. 307; published erratum p. 6,
    book p. 307 line 26. This supporting
    scalar maximization retains both printed branches
    and every nonnegative ordered unit direction. *)
Theorem critical_corrected_projection_scalar_bound (R:realType) (u v:R):
  0<=v ->v<=u ->u^+2+v^+2= 1 ->
  (if v<=u/2 then 2*(u/4+v) else 3*u/2)<=3/Num.sqrt 5.
Proof.
move=>hv hvu hUnit.
have hu:0<=u:=le_trans hv hvu.
have hFive:0<(5:R) by rewrite ltr0n.
have hRoot:0<Num.sqrt (5:R) by rewrite sqrtr_gt0.
have hRootSquare:Num.sqrt (5:R)^+2= 5:=sqr_sqrtr (ltW hFive).
have hNZ:Num.sqrt (5:R)!=0 by rewrite gt_eqF.
have hTarget:0<3/Num.sqrt (5:R) by rewrite divr_gt0 // ltr0n.
have hTargetSquare:(3/Num.sqrt (5:R))^+2= 9/5.
  rewrite expr_div_n hRootSquare;ring.
case:ifP=>hBranch.
- have hFirst:0<=(u-2*v)*(31*u+22*v).
    apply:mulr_ge0;[move:hBranch;lra|nra].
  have hValue:0<=2*(u/4+v) by nra.
  nra.
- have hUpper:u/2<v by rewrite ltNge hBranch.
  have hFirst:0<=(2*v-u)*(2*v+u) by apply:mulr_ge0;nra.
  have hValue:0<=3*u/2 by nra.
  nra.
Qed.

(** Source for [critical_projection_extremal_direction]:
    the original slope-one-half direction realizes
    the corrected scalar upper bound, supporting
    the projection directions U in 3.3.20,
    p. 307 and published erratum p. 6,
    book p. 307 line 26. Actual projection
    and measure identities are proved separately. *)
Lemma critical_projection_extremal_direction (R:realType):
  let u:=(2:R)/Num.sqrt 5 in let v:=(1:R)/Num.sqrt 5 in
  0<v /\v<=u /\u^+2+v^+2= 1 /\v=u/2 /\
    2*(u/4+v)=3/Num.sqrt 5 /\3*u/2=3/Num.sqrt 5.
Proof.
move=>u v.
have hFive:0<(5:R) by rewrite ltr0n.
have hRoot:0<Num.sqrt (5:R) by rewrite sqrtr_gt0.
have hRootSquare:Num.sqrt (5:R)^+2= 5:=sqr_sqrtr (ltW hFive).
have hNZ:Num.sqrt (5:R)!=0 by rewrite gt_eqF.
have hv:0<v by rewrite /v divr_gt0.
have hRatio:v=u/2 by rewrite /u /v;field.
have hLength:2*(u/4+v)=3/Num.sqrt 5 by rewrite /u /v;field.
have hOther:3*u/2=3/Num.sqrt 5 by rewrite /u;field.
have hUnit:u^+2+v^+2= 1.
  by rewrite /u /v !expr_div_n hRootSquare;field;rewrite ?hNZ ?pnatr_eq0.
have hvu:v<=u by rewrite hRatio;lra.
exact:(conj hv (conj hvu (conj hUnit (conj hRatio (conj hLength hOther))))).
Qed.
