(** Federer (1969), 4.1.4, pp. 348–349: the components
    about a fixed centre in a directed open exhaustion cover
    the original connected domain. This supplies the implicit
    eventual compact-support step and the relatively compact
    localization, using the earlier norm-ball connectedness
    and public component laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormLinearDomainLaws NormConvexConnected NormOpenComponents ComponentInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DirectedOpenComponentExhaustion.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation T := (real_norm_metric_space hNX).
Variable I:choiceType.
Variable P:set I.
Variable A:set X.
Variable O:I->set X.
Hypothesis hOpen:forall i,P i ->@open T (O i).
Hypothesis hInside:forall i,P i ->O i `<=` A.
Hypothesis hCover:forall x,A x ->exists i,P i /\ O i x.
Hypothesis hDirected:forall i j,P i ->P j ->
  exists k,P k /\ (O i `<=` O k) /\ (O j `<=` O k).
Variable a:X.
Hypothesis ha:A a.
Local Notation C := (fun i=>@connected_component T (O i) a).

(** Source for [directed_open_components_exhaust_connected]:
    every point of connected A belongs to one original
    fixed-centre component in a directed open exhaustion,
    the exhaustion inference in Federer 4.1.4, pp. 348–349. *)
Theorem directed_open_components_exhaust_connected:
  @connected T A ->forall x,A x ->exists i,P i /\ C i x.
Proof.
move=>hConnected.
pose E:set X:=\bigcup_(i in P) C i.
pose D:set X:=[set x|A x /\ ~E x].
have hEInside:E `<=` A.
  move=>x [i hi hx].
  exact:(@hInside i hi x (@connected_component_sub T (O i) a x hx)).
have hENonempty:E !=set0.
  have[i [hi hia]]:=@hCover a ha.
  exists a; exists i; first exact hi.
  exact:(@connected_component_refl T (O i) a hia).
have hOpenE:@open T E.
  apply:bigcup_open=>i hi.
  exact:(@norm_open_components_open R X NX hNX (O i) a (@hOpen i hi)).
have hOpenD:@open T D.
  rewrite openE=>x [hx hNotE].
  have[i [hi hxi]]:=@hCover x hx.
  have hNbhs:nbhs (x:T) (O i).
    move:(@hOpen i hi); rewrite openE; exact.
  have[r [hr hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX (O i) x).2 hNbhs.
  pose B:set X:=[set y|NX (y-x)<r].
  have hxB:B x.
    change (is_true (NX (x-x)<r)).
    by rewrite subrr (real_seminorm_zero hNX.1).
  have hBInside:B `<=` O i.
    move=>y hy; have h:=hBall (y-x) hy; by rewrite addrC subrK in h.
  have hBConnected:@connected T B.
    exact:(@norm_inner_convex_connected R X NX hNX B (@norm_open_ball_convex R X NX hNX x r)).
  apply/(metricType_numDomainType.nbhs_mdistP (x:T) _).
  exists r; first exact hr.
  move=>z hz.
  have hzB:B z.
    change (is_true (NX (x-z)<r)) in hz.
    change (is_true (NX (z-x)<r)).
    by rewrite (real_seminorm_subtract hNX.1).
  split; first exact:(@hInside i hi z (hBInside z hzB)).
  move=>[j hj hzC].
  have[k [hk [hik hjk]]]:=@hDirected i j hi hj.
  have hzK:C k z:=@component_inclusion T (O j) (O k) a hjk z hzC.
  have hBK:B `<=` O k by move=>y hy; exact:hik y (hBInside y hy).
  have hBC:B `<=` @connected_component T (O k) z.
    exact:(@connected_component_max T (O k) B z hzB hBK hBConnected).
  have hSame:C k=@connected_component T (O k) z.
    exact:(@same_connected_component T (O k) a z hzK).
  have hxK:C k x by rewrite hSame; exact:hBC x hxB.
  apply:hNotE; exists k; first exact hk; exact hxK.
have hRelativeOpen:exists2 V:set T,@open T V & E=A `&` V.
  exists E; first exact hOpenE.
  apply/seteqP; split.
  - move=>x hx; split; first exact:hEInside x hx; exact hx.
  - by move=>x [_ hx].
have hRelativeClosed:exists2 V:set T,@closed T V & E=A `&` V.
  exists (~` D); first exact:open_closedC hOpenD.
  apply/seteqP; split.
  - move=>x hx; split; first exact:hEInside x hx.
    move=>[_ hNot]; exact:hNot hx.
  - move=>x [hx hNot]; apply:contrapT=>hNe; apply:hNot; by split.
have hWhole:E=A:=@hConnected E hENonempty hRelativeOpen hRelativeClosed.
move=>x hx.
have hEx:E x by rewrite hWhole.
have[i hi hxi]:=hEx; exists i; by split.
Qed.
End DirectedOpenComponentExhaustion.
