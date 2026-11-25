(** Federer (1969), 3.4.2(6)–(7), pp. 312–313: differential laws
    of the original projection retraction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import TensorUP Hom ModuleQuotient GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric RealNormUP
  NormDifferentialUP NormDifferentialLinear NormDifferentialFiniteCalculus
  NormDifferentialLocal NormDifferentialDirectional NormVanishingTangent
  TangentConeUP TangentConeBasic TangentOpenDomain TangentDifferentialImage
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalChartRetractionClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_retraction_differential_projection]:
    differentiating p composed with r=p supports Dr(Z) contained in Z
    in 3.4.2(6), p. 312. Every differential is the genuine one on U. *)
Theorem critical_retraction_differential_projection (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g a (D:Hom (R_n R m) (R_n R m)):
  is_critical_manifold_chart k Z S p g ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) a D ->
  forall v,euclidean_projection_linear p (D v)=euclidean_projection_linear p v.
Proof.
move=>hChart hD.
pose X:=R_n R m;pose V:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NV:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose P:=hom_of_linear (euclidean_projection_linear p).
pose U:=fun x=>(euclidean_projection_linear p @` S) (P x).
pose r:=fun x=>g (P x).
have hBound:norm_bounded_linear NX NV P:=critical_projection_bounded_linear p.
have hPost:=@norm_differential_postcompose R X X V NX NX NV hNX U r a D P hD hBound.
have hEqual x (hx:U x):P (r x)= P x:=(critical_chart_right_inverse hChart hx).2.
have hComp:=@norm_differential_domain_agreement R X V NX NV hNX U
  (fun x=>P (r x)) P a (hom_comp P D) hEqual hPost.
have hLinear:=@norm_differential_linear R X V NX NV hNX hNV U a P
  (norm_differential_interior hD) hBound.
have he:=norm_differential_unique hNX hNV hComp hLinear.
move=>v;exact:(congr1 (fun L:Hom X V=>L v) he).
Qed.

(** Source for [critical_retraction_differential_preserves_subspace]:
    Dr(x) maps Z into Z, the second assertion in the first display
    of 3.4.2(6), p. 312. Its projection identity puts Dr(z)-z in
    ker p; the original chart puts that kernel in Z. *)
Lemma critical_retraction_differential_preserves_subspace (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g a (D:Hom (R_n R m) (R_n R m)):
  is_critical_manifold_chart k Z S p g ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) a D ->
  forall z,Z z ->Z (D z).
Proof.
move=>hChart hD z hz.
have hP:=critical_retraction_differential_projection hChart hD z.
have hKernel:euclidean_projection_linear p (D z-z)=0 by rewrite linearB hP subrr.
have hDiff:=critical_chart_kernel hChart hKernel.
have hSum:=subspace_add hDiff hz.
by rewrite subrK in hSum.
Qed.

(** Source for [critical_retraction_differential_tangent]: Dr(x)v is
    tangent to S at r(x), as used for the curve g in 3.4.2(6),
    p. 312. The image inclusion follows from the actual differential
    image theorem of 3.1.21; no tangent plane is supplied as a premise. *)
Theorem critical_retraction_differential_tangent (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g a (D:Hom (R_n R m) (R_n R m)):
  is_critical_manifold_chart k Z S p g ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) a D ->
  forall v,norm_tangent_cone (inner_norm (@euclidean_inner_productP R m)) S
    (g (euclidean_projection_linear p a)) (D v).
Proof.
move=>hChart hD v.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
have hTan:norm_tangent_cone NX U a v.
  by rewrite (norm_tangent_open_domain hNX (norm_differential_interior hD)).
have hImage:=@norm_differential_tangent_image R X X NX NX hNX hNX U U r a D hD v hTan.
have hSub:r @` (U `&` U) `<=` S.
  move=>y [x [hx _] <-];exact:(critical_chart_right_inverse hChart hx).1.
exact:(@norm_tangent_mono R X NX _ _ (r a) hSub (D v) hImage).
Qed.

(** Source for [critical_retraction_differential_fixes_tangent]:
    Dr(x)z=z on Tan(S,x), the identity used to expand z in the
    basis of Z in 3.4.2(7), p. 313. On S, r agrees with the identity;
    the relative uniqueness theorem of 3.1.22 identifies their tangent
    derivatives. *)
Theorem critical_retraction_differential_fixes_tangent (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g a (D:Hom (R_n R m) (R_n R m)):
  is_critical_manifold_chart k Z S p g ->S a ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (fun x=>g (euclidean_projection_linear p x)) a D ->
  forall z,norm_tangent_cone (inner_norm (@euclidean_inner_productP R m)) S a z ->D z=z.
Proof.
move=>hChart ha hD.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
pose I:=hom_of_linear (@linear_id R X).
have hBound:norm_bounded_linear NX NX I.
  exists 1;split;first exact:ler01.
  by move=>x;rewrite mul1r.
have hI:=@norm_differential_linear R X X NX NX hNX hNX U a I
  (norm_differential_interior hD) hBound.
have hClosure:@closure (real_norm_metric_space hNX) S a:=subset_closure ha.
have hEqual x (hx:S x) (hxU:U x) (hxU':U x):r x= I x.
  exact:(critical_chart_left_inverse hChart hx).
exact:(@norm_differentials_agree_on_tangent R X X NX NX hNX hNX U U S r I a D I
  hD hI hClosure hEqual).
Qed.
