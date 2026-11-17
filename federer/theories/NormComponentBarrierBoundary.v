(** Federer (1969), 3.4.8(11), p. 333:
    the original Psi vanishes on the boundary
    of each component of the ball outside Phi=0.
    The boundary is either on the sphere
    or on the original zero set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormOpenDomainLaws NormBoundedLinearTopology NormClassZeroNonzeroLocus
  NormOpenComponentBoundary MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_component_barrier_boundary_zero]:
    the complete boundary equation Psi=0
    used in the component maximum argument,
    3.4.8(11), p. 333. *)
Theorem norm_component_barrier_boundary_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) (phi:X->R^o) (epsilon:R):
  norm_class_zero NX (fun z:R^o=>`|z|) A phi ->
  (forall x,NX x<=epsilon ->A x) ->
  let S:set X:=[set x|NX x<epsilon /\ phi x<>0] in
  forall a x,@closure (real_norm_metric_space hNX)
      (@connected_component (real_norm_metric_space hNX) S a) x ->
    ~@interior (real_norm_metric_space hNX)
      (@connected_component (real_norm_metric_space hNX) S a) x ->
    (epsilon^+2-(NX x)^+2)*(phi x)^+2 = 0.
Proof.
move=>hPhi hKA S a x hClosure hNotInterior.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose K:set X:=[set y|NX y<=epsilon].
have hKBall:K = @metric_closed_ball R (real_norm_metric_space hNX) 0 epsilon.
  apply/seteqP;split=>y hy.
  - change (NX (0-y)<=epsilon);by rewrite sub0r (real_seminorm_negate hNX.1).
  - change (is_true (NX (0-y)<=epsilon)) in hy.
    by rewrite sub0r (real_seminorm_negate hNX.1) in hy.
have hKClosed:@closed T K.
  rewrite hKBall;exact:metric_closed_ball_closed.
have hSK:S `<=` K by move=>y [hy hNonzero];exact:ltW hy.
have hCK:@connected_component T S a `<=` K.
  move=>y hy;exact:hSK y (@connected_component_sub T S a y hy).
have hKx:K x:=hKClosed x (@closureS T _ K hCK x hClosure).
have hSOpen:@open T S.
  have hNonzeroOpen:=@norm_class_zero_nonzero_locus_open R X R^o NX (fun z:R^o=>`|z|)
    hNX (@scalar_absolute_value_norm R) A phi hPhi.
  have hBall:@open T [set y|NX y<epsilon].
    rewrite openE=>y hy.
    apply:(@norm_domain_interior_neighbourhood R X NX hNX _ y).1.
    have h:=@norm_open_ball_domain_interior R X NX hNX 0 epsilon y.
    have hY:NX (y-0)<epsilon by rewrite subr0.
    have [r [hr hSmall]]:=h hY;exists r;split;first exact:hr.
    move=>v hv;have hMem:=hSmall v hv;by rewrite subr0 in hMem.
  have hSame:S = [set y|NX y<epsilon] `&` [set y|A y /\ phi y!=0].
    apply/seteqP;split.
    + move=>y [hy hNonzero];split;first exact:hy.
      split;first exact:hKA y (ltW hy).
      by apply/eqP.
    + move=>y [hy [hAy hNonzero]];split;first exact:hy.
      move=>hZero;move:hNonzero;by rewrite hZero eqxx.
  rewrite hSame;exact:openI hBall hNonzeroOpen.
have hOutside:=@norm_open_component_boundary_outside R X NX hNX S a x hSOpen hClosure hNotInterior.
case:(ltP (NX x) epsilon)=>hInside.
- have hZero:phi x = 0.
    apply:contrapT=>hNonzero;apply:hOutside;by split.
  by rewrite hZero expr0n mulr0.
- have hSphere:NX x = epsilon.
    apply:le_anti;apply/andP;by split.
  by rewrite hSphere subrr mul0r.
Qed.
