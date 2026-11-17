(** Federer (1969), 3.4.12, p. 339: identify the
    underlying real manifold with its paired Euclidean coordinates.
    Reuse the original straightening charts, bounded linear inverse
    maps, diffeomorphism composition, and the proved plane-image theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ModuleQuotient LinearBasis GrassmannSubspaces
  GrassmannInjectiveImage NormDifferentialUP NormBoundedLinearTopology NormOpenDomainLaws
  NormClassOneUP NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticLinear NormAnalyticOperations
  NormDiffeomorphismUP NormDiffeomorphismComposition NormDiffeomorphismRestriction NormDiffeomorphismSourceRestriction
  NormAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [norm_analytic_submanifold_linear_coordinates]: an
    invertible bounded linear identification preserves the actual
    analytic manifold dimension, supporting the doubled real dimension
    statement of 3.4.12, p. 339. No real or complex
    dimension comparison is assumed by this chart connection. *)
Theorem norm_analytic_submanifold_linear_coordinates (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (u:Hom X Y) (v:Hom Y X) n (e:'I_n->Y) (he:is_basis e) m (S:set X):
  norm_bounded_linear NX NY u ->norm_bounded_linear NY NX v ->cancel u v ->cancel v u ->
  is_norm_analytic_submanifold hNX m S ->
  is_norm_analytic_submanifold hNY m (v @^-1` S).
Proof.
move=>hU hV hUV hVU hS b hb.
pose TX:=Topological.clone (real_norm_metric_space hNX) _.
pose TY:=Topological.clone (real_norm_metric_space hNY) _.
have [T [C [s [t [Z [hTb [hD [hSAnalytic [hTAnalytic hImage]]]]]]]]]:=hS (v b) hb.
have hTInterior x (hx:T x):norm_domain_interior NX T x.
  have hOpen:=norm_analytic_domain_open hSAnalytic;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX T x).2 (hOpen x hx).
have hCInterior x (hx:C x):norm_domain_interior NX C x.
  have hOpen:=norm_analytic_domain_open hTAnalytic;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX C x).2 (hOpen x hx).
pose W:set Y:=v @^-1` T.
have hVContinuous:=@norm_bounded_linear_continuous R Y X NY NX hNY hNX v hV.
have hWOpen:@open TY W:=@open_comp TY TX v T (fun x _=>hVContinuous x)
  (norm_analytic_domain_open hSAnalytic).
have hWInterior y (hy:W y):norm_domain_interior NY W y.
  have hOpen:=hWOpen;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R Y NY hNY W y).2 (hOpen y hy).
have hWb:W b:=@norm_domain_interior_member R X NX hNX T (v b) hTb.
have hLinearVU:=@norm_linear_diffeomorphism R Y X NY NX hNY hNX v u 1%N hV hU hVU hUV.
have hRestrictedVU:=@norm_diffeomorphism_target_restriction R Y X NY NX hNY hNX setT setT T v u 1%N
  hLinearVU (fun _ _=>Logic.I) hTInterior.
have hDomain:[set y:Y|setT y /\T (v y)] = W.
  apply:funext=>y;apply:propext;split;[by case|by move=>hy;split].
change (is_norm_diffeomorphism hNY hNX [set y:Y|setT y /\T (v y)] T v u 1%N) in hRestrictedVU.
rewrite hDomain in hRestrictedVU.
have hFirst:=@norm_diffeomorphism_composition R Y X X NY NX NX hNY hNX hNX
  W T C v u s t 1%N hRestrictedVU hD.
have hLinearUV:=@norm_linear_diffeomorphism R X Y NX NY hNX hNY u v 1%N hU hV hUV hVU.
have hRestrictedUV:=@norm_diffeomorphism_source_restriction R X Y NX NY hNX hNY setT C setT u v 1%N
  hLinearUV (fun _ _=>Logic.I) hCInterior.
pose D:set Y:=fun y=>True /\C (v y).
have hFinal:=@norm_diffeomorphism_composition R Y X Y NY NX NY hNY hNX hNY
  W C D (fun y=>s (v y)) (fun x=>u (t x)) u v 1%N hFirst hRestrictedUV.
have hVAnalytic:=@norm_bounded_linear_analytic R Y X NY NX hNY hNX W hWInterior v hV.
have hSV:=@norm_analytic_compose_on R Y X X NY NX NX hNY hNX hNX W T v s
  (fun y hy=>hy) hVAnalytic hSAnalytic.
have hUAnalytic:=@norm_bounded_linear_analytic R X Y NX NY hNX hNY setT
  (fun x _=>norm_full_domain_interior NX x) u hU.
have hForward:=@norm_analytic_compose_on R Y X Y NY NX NY hNY hNX hNY W setT
  (fun y=>s (v y)) u (fun _ _=>Logic.I) hSV hUAnalytic.
have hDInterior y (hy:D y):norm_domain_interior NY D y.
  have hc:=norm_class_continuous (norm_diffeomorphism_inverse_class hFinal).
  exact:(@hc y hy).1.
have hVDAnalytic:=@norm_bounded_linear_analytic R Y X NY NX hNY hNX D hDInterior v hV.
have hTV:=@norm_analytic_compose_on R Y X X NY NX NX hNY hNX hNX D C v t
  (fun y hy=>hy.2) hVDAnalytic hTAnalytic.
have hBackward:=@norm_analytic_compose_on R Y X Y NY NX NY hNY hNX hNY D setT
  (fun y=>t (v y)) u (fun _ _=>Logic.I) hTV hUAnalytic.
have [Znew hZnew]:=@grassmann_injective_image R X Y m Z u n e he (can_inj hUV).
exists W,D,(fun y=>u (s (v y))),(fun y=>u (t (v y))),Znew.
split;first exact:hWInterior b hWb.
split;first exact:hFinal.
split;first exact:hForward.
split;first exact:hBackward.
apply/seteqP;split.
- move=>z [y [hSy hWy] <-];split.
  + rewrite hZnew;exists (s (v y));last reflexivity.
    have h:(s @` (S `&` T)) (s (v y)) by exists (v y);first split.
    rewrite hImage in h;exact:h.1.
  + split;first exact:Logic.I;rewrite hUV.
    exact:(@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t 1%N hD (v y) hWy).
- move=>z [hZz [_ hCz]].
  rewrite hZnew in hZz;have [w hWZ hWZz]:=hZz.
  have hVZ:grassmann_val Z (v z) by rewrite -hWZz hUV.
  have h:(s @` (S `&` T)) (v z) by rewrite hImage;split.
  have [x [hSx hTx] hSX]:=h.
  exists (u x).
  + split;[change (S (v (u x)))|change (T (v (u x)))];by rewrite hUV.
  + by rewrite hUV hSX hVU.
Qed.
