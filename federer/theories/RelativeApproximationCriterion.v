(** Federer (1969), 3.1.22, p. 235: the relative
    first-order remainder criterion, with the base value corrected
    by the erratum p. 4, book p. 235 line 19. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormOpenDomainLaws TangentConeUP PartialFunctionUP RelativeDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [relative_differential_first_order_approximation]:
    the forward implication of the displayed remainder criterion
    in Federer 3.1.22, p. 235. The ambient extension
    gives eta=g(a), and agreement at a proves the erratum's
    condition eta=f(a) when a is in S. *)
Theorem relative_differential_first_order_approximation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (A S:set X) (f:X->Y) a (L:partial_function X Y) :
  @has_relative_norm_differential R X Y NX NY hNX A S f a L ->
  exists eta (D:Hom X Y),has_relative_first_order_approximation NX NY A S f a eta D /\
    is_tangent_differential_restriction NX S a D L.
Proof.
move=>[hcl [U [g [D [hg [hfg hDL]]]]]].
have haU:=norm_domain_interior_member hNX (norm_differential_interior hg).
have [r [hr hU]]:=norm_differential_interior hg.
exists (g a),D; split; last exact hDL.
split; first exact: norm_differential_bounded hg.
split; first by move=>haS; exact: (hfg a haS haU).2.
split.
- exists r; split=>// x hxS hx.
  have hxU:U x by have hh:=hU (x-a) hx; rewrite addrC subrK in hh.
  exact (hfg x hxS hxU).1.
- move=>e he; have [d [hd hrem]]:=norm_differential_remainder hg he.
  exists (Num.min r d); split; first by rewrite lt_min hr hd.
  move=>x hxS hpos hsmall.
  have /andP [hxr hxd]: (NX (x-a)<r) && (NX (x-a)<d) by rewrite -lt_min.
  have hshift:a+(x-a)=x by rewrite addrC subrK.
  have hxU:U x by rewrite -hshift; exact: hU (x-a) hxr.
  have hh:=hrem (x-a); rewrite hshift in hh.
  rewrite (hfg x hxS hxU).2.
  exact (hh hxU hxd).
Qed.

(** Source for [relative_approximation_extension]: the extension
    g=f on S and g(x)=eta+D(x-a) off S in Federer
    3.1.22, p. 235. The existence proof includes
    the erratum's base-value condition and covers the zero
    increment and base points in Clos S outside the f-domain. *)
Theorem relative_approximation_extension (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) a eta (D:Hom X Y) :
  has_relative_first_order_approximation NX NY A S f a eta D ->
  exists (U:set X) (g:X->Y),
    has_norm_differential NX NY U g a D /\ g a=eta /\
    (forall x,S x -> U x -> A x /\ f x=g x).
Proof.
move=>[hD [hbase [[r [hr hdom]] hrem]]].
pose g:=fun x=>if `[<S x>] then f x else eta+D (x-a).
have hga:g a=eta.
  rewrite /g; case:ifP=>[/asboolP ha|ha].
  - exact: hbase ha.
  - by rewrite subrr linear0 addr0.
have hg:has_norm_differential NX NY setT g a D.
  constructor.
  - exact: norm_full_domain_interior.
  - exact hD.
  - move=>e he; have [d [hd hb]]:=hrem e he.
    exists d; split=>// h _ hsmall.
    case:(eqVneq h 0)=>[->|hn].
    + by rewrite addr0 subrr linear0 subrr (real_seminorm_zero hNY.1)
        (real_seminorm_zero hNX.1) mulr0.
    + have hp:0<NX h by rewrite (real_norm_positive hNX.1 hNX.2).
      rewrite hga /g; case:ifP=>[/asboolP hxS|hxS].
      * have hh:=hb (a+h) hxS.
        rewrite addrAC subrr add0r in hh.
        exact: hh hp hsmall.
      * have hshift:(a+h)-a=h by rewrite addrAC subrr add0r.
        rewrite hshift [eta+D h]addrC addrK subrr (real_seminorm_zero hNY.1).
        exact (mulr_ge0 (ltW he) (real_seminorm_nonnegative hNX.1 h)).
pose U:=fun x=>NX (x-a)<r.
have hUa:norm_domain_interior NX U a.
  apply: (@norm_open_ball_domain_interior R X NX hNX a r a).
  by rewrite subrr (real_seminorm_zero hNX.1).
have hgU:=@norm_differential_restrict R X Y NX NY setT U g a D (fun _ _=>I) hUa hg.
exists U,g; split=>//; split=>// x hxS hxU.
split; first exact: hdom x hxS hxU.
by rewrite /g (asboolT hxS).
Qed.

(** Source for [relative_norm_differential_remainder_criterion]:
    the full equivalence between ambient extension and the
    displayed relative remainder condition in Federer 3.1.22,
    p. 235, with the base-value correction of the
    erratum p. 4, book p. 235 line 19. The
    relative differential remains the restriction to the exact cone. *)
Theorem relative_norm_differential_remainder_criterion (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) a (L:partial_function X Y) :
  @closure (real_norm_metric_space hNX) S a ->
  (@has_relative_norm_differential R X Y NX NY hNX A S f a L <->
    exists eta (D:Hom X Y),has_relative_first_order_approximation NX NY A S f a eta D /\
      is_tangent_differential_restriction NX S a D L).
Proof.
move=>hcl; split; first exact: relative_differential_first_order_approximation.
move=>[eta [D [happ hDL]]].
have [U [g [hg [hga hfg]]]]:=@relative_approximation_extension R X Y NX NY hNX hNY A S f a eta D happ.
split; first exact hcl.
exists U,g,D; split=>//; by split.
Qed.
