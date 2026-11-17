(** Federer (1969), 3.4.10, p. 337:
    analytic manifold pieces remain analytic after
    translating the source. Reuse the original
    chart definition of 3.1.19(1), p. 231,
    its analytic version in 3.1.24, p. 240,
    and the existing diffeomorphism composition laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormBoundedLinearTopology NormOpenDomainLaws NormDiffeomorphismUP
  NormDiffeomorphismRestriction NormDiffeomorphismComposition NormTranslationDiffeomorphism
  EuclideanSubmanifoldUP AnalyticSubmanifoldUP NormAnalyticUP NormAnalyticLocal
  NormAnalyticTranslation NormAnalyticComposition NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_source_translation]: the
    translated analytic pieces used in the
    all-centre cover of 3.4.10, p. 337.
    Compose each original chart with the
    actual translation and its inverse; retain
    its original vector plane and dimension. *)
Theorem analytic_submanifold_source_translation (R:realType) n m
    (S:set (R_n R n)) (c:R_n R n):
  @is_euclidean_analytic_submanifold R n m S ->
  @is_euclidean_analytic_submanifold R n m [set x|S (x-c)].
Proof.
move=>hS b hb.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose M:=Topological.clone (real_norm_metric_space hNX) _.
pose u:=fun x:M=>(x-c:M).
pose v:=fun x:M=>(x+c:M).
have hUContinuous:continuous u.
  have hSame:u=(fun x:X=>-c+x) by apply:funext=>x;rewrite /u addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hUV:cancel v u by move=>x;rewrite /u /v addrK.
have hVU:cancel u v by move=>x;rewrite /u /v subrK.
have [T [C [sigma [tau [Z [hChart [hSigma hTau]]]]]]]:=hS (u b) hb.
have [hTb hD hImage]:=hChart.
pose W:set X:=u @^-1` T.
have hTInterior x (hx:T x):norm_domain_interior NX T x.
  have hOpen:=norm_analytic_domain_open hSigma;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX T x).2 (hOpen x hx).
have hWOpen:@open M W:=@open_comp M M u T (fun x _=>hUContinuous x)
  (norm_analytic_domain_open hSigma).
have hWInterior x (hx:W x):norm_domain_interior NX W x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  have h:=hWOpen;rewrite openE in h;exact:h x hx.
have hSame:[set x:X|setT x /\T (u x)]=W.
  apply:funext=>x;apply:propext;split;[by case|by move=>hx;split].
have hTranslation:=@norm_translation_diffeomorphism R X NX hNX c 1%N.
have hRestricted:=@norm_diffeomorphism_target_restriction R X X NX NX hNX hNX
  setT setT T u v 1%N hTranslation (fun _ _=>Logic.I) hTInterior.
change (is_norm_diffeomorphism hNX hNX [set x:X|setT x /\T (u x)] T u v 1%N) in hRestricted.
rewrite hSame in hRestricted.
have hComposite:=@norm_diffeomorphism_composition R X X X NX NX NX hNX hNX hNX
  W T C u v sigma tau 1%N hRestricted hD.
have [hVAnalytic hUAnalytic]:=@norm_translations_analytic R X NX hNX setT
  (fun x _=>norm_full_domain_interior NX x) c.
have hSigmaU:=@norm_analytic_composition R X X X NX NX NX hNX hNX hNX
  setT T u sigma hUAnalytic hSigma.
change (@norm_analytic R X X NX NX hNX hNX [set x:X|setT x /\T (u x)]
  (fun x=>sigma (u x))) in hSigmaU.
rewrite hSame in hSigmaU.
have hVTau:=@norm_analytic_compose_on R X X X NX NX NX hNX hNX hNX
  C setT tau v (fun _ _=>Logic.I) hTau hVAnalytic.
exists W,C,(fun x=>sigma (u x)),(fun y=>v (tau y)),Z;split;last by split.
constructor.
- have hbT:T (u b):=@norm_domain_interior_member R X NX hNX T (u b) hTb.
  exact:(hWInterior b hbT).
- exact:hComposite.
- rewrite -hImage;apply/seteqP;split.
  + move=>y [x [hxS hxW] hXY];exists (u x);last exact:hXY.
    by split.
  + move=>y [x [hxS hxT] hXY];exists (v x).
    * split.
      -- change (S (u (v x)));by rewrite hUV.
      -- change (T (u (v x)));by rewrite hUV.
    * by rewrite hUV.
Qed.
