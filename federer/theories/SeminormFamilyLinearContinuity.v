(** Federer (1969), 4.1.1, pp. 344–345: continuity of linear
    maps is equivalent to finite bounds by the defining seminorms.
    This supporting form treats arbitrary seminorm-generated source
    and target spaces; the scalar target gives the printed criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP RealSeminormOperations OpenFamilyTopologyUP
  DirectedSeminormFamilyUP DirectedSeminormTopology SeminormBallDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SeminormLinearContinuity.
Variable R:realType.
Variables E F:lmodType R.
Variables I J:Type.
Variable p:I->E->R.
Variable q:J->F->R.
Variables (O:set (set E)) (Q:set (set F)).
Hypothesis hp:is_directed_seminorm_family p.
Hypothesis hq:is_directed_seminorm_family q.
Hypothesis hO:is_seminorm_family_topology p O.
Hypothesis hQ:is_seminorm_family_topology q Q.
Variable L:Hom E F.

(** Source for [seminorm_family_continuous_linear_bound]: a
    continuous linear map has a finite bound for each target
    seminorm, supporting T <= M nu^i_K in Federer 4.1.1, p. 344. *)
Theorem seminorm_family_continuous_linear_bound :
  open_family_continuous O Q L -> forall j,exists i C,
    0<=C /\ forall x,q j (L x)<=C * p i x.
Proof.
move=>hL j.
have hBall:Q [set y|q j y<1].
  have h:=seminorm_family_ball_open hq hQ j (0:F) 1.
  have he:[set y:F|q j (y-0)<1]=[set y:F|q j y<1].
    by apply:funext=>y; rewrite /= subr0.
  by rewrite he in h.
have hPre:=hL _ hBall.
have hZero:([set x:E|q j (L x)<1]) 0.
  by rewrite /= linear0 (real_seminorm_zero (directed_seminorm_laws hq j)).
have [i [d [hd hb]]]:=(hO.2 _).1 hPre 0 hZero.
have hSmall x:p i x<d -> q j (L x)<1.
  move=>hx; apply:hb; by rewrite /= subr0.
exists i,(2/d); split; first by apply:ltW; rewrite divr_gt0 // ltr0n.
exact:(seminorm_unit_ball_domination (directed_seminorm_laws hp i)
  (real_seminorm_linear_precompose (directed_seminorm_laws hq j) (hom_linear L)) hd hSmall).
Qed.

(** Source for [seminorm_family_bounded_linear_continuous]:
    finite seminorm bounds imply continuity of the linear map,
    supporting the converse continuity criterion in Federer
    4.1.1, pp. 344–345. Zero bounds and seminorms are included. *)
Theorem seminorm_family_bounded_linear_continuous :
  (forall j,exists i C,0<=C /\ forall x,q j (L x)<=C * p i x) ->
  open_family_continuous O Q L.
Proof.
move=>hBound A hA; apply:(hO.2 _).2=>x hx.
have [j [r [hr hBall]]]:=(hQ.2 A).1 hA (L x) hx.
have [i [C [hC hB]]]:=hBound j.
have hC1:0<C+1 by lra.
exists i,(r/(C+1)); split; first by rewrite divr_gt0.
move=>y hy; apply:(hBall (L y)); rewrite -linearB.
have hSmall:(C+1) * p i (y-x)<r.
  by move:hy; rewrite ltr_pdivlMr // mulrC.
have hNonneg:=real_seminorm_nonnegative (directed_seminorm_laws hp i) (y-x).
have hCmp:C * p i (y-x)<=(C+1) * p i (y-x) by nra.
exact:le_lt_trans (hB (y-x)) (le_lt_trans hCmp hSmall).
Qed.

(** Source for [seminorm_family_linear_continuity_iff]: the exact
    finite-seminorm criterion for linear continuity, supporting
    both continuous duals in Federer 4.1.1, pp. 344–345. *)
Theorem seminorm_family_linear_continuity_iff :
  open_family_continuous O Q L <->
  forall j,exists i C,0<=C /\ forall x,q j (L x)<=C * p i x.
Proof.
split; [exact:seminorm_family_continuous_linear_bound|
  exact:seminorm_family_bounded_linear_continuous].
Qed.
End SeminormLinearContinuity.
