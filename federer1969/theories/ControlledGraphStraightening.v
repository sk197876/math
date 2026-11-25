(** Federer (1969), 3.1.23, pp. 236–237: the
    controlled supported diffeomorphism from an orthogonal graph chart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra ring.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates RealNormUP
  EuclideanInnerProduct InnerNorm HilbertFormCompactness OrthogonalMaps AdjointUP AdjointCriteria ProjectionNorm
  NormMetric FiniteNormEquivalence NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  NormDifferentialChain NormClassOneUP NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormOpenDomainLaws AnnularCutoffUP AnnularCutoffSealed AnnularCutoffScaling ScaledCutoffUP
  GraphDefectCalculus GraphDefectSmall CutoffGraphCorrectionClass CutoffGraphCorrectionBound
  GraphCorrectionPlane ProjectedGraphTangent SupportedStraighteningUP EuclideanSupportedDiffeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [controlled_graph_straightening]: the construction
    and all estimates of Federer 3.1.23, pp. 236–237,
    from the actual chart of 3.1.19(5). Unlike the
    printed normalization b= 0, translations are retained throughout.
    The cutoff is opaque and all its needed laws are proved.
    The final target is the actual affine tangent plane. *)
Theorem controlled_graph_straightening (R:realType) n mu k
    (B T:set (R_n R n)) b t
    (p:{linear R_n R n->R_n R mu}) (j:{linear R_n R mu->R_n R n})
    (psi:R_n R mu->R_n R n) :
  (1<=k)%N -> B b -> 0<t<1 ->
  norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) T b ->
  is_orthogonal_map (@euclidean_inner_product R mu) (@euclidean_inner_product R n) j ->
  is_adjoint (@euclidean_inner_product R mu) (@euclidean_inner_product R n) j p ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (p @` T) psi k ->
  (forall z,(p @` T) z -> B (psi z) /\ T (psi z)) ->
  (forall z,(p @` T) z -> p (psi z)= z) ->
  (forall x,B x -> T x -> psi (p x)= x) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R n)) (p @` T) psi (p b) (hom_of_linear j) ->
  exists rho:R,0<rho /\ forall r:R,0<r -> r<rho -> exists F g,
    is_controlled_tangent_straightening
      (inner_norm_real_norm (@euclidean_inner_productP R n)) B b t r F g k.
Proof.
move=>hk hb ht hTb hj hp hpsi hrange hcan hinv hBase.
pose X:= R_n R n; pose Z:= R_n R mu.
pose hBX:=@euclidean_inner_productP R n.
pose hBZ:=@euclidean_inner_productP R mu.
pose NX:= inner_norm hBX; pose NZ:= inner_norm hBZ.
pose hNX:= inner_norm_real_norm hBX; pose hNZ:= inner_norm_real_norm hBZ.
pose M:= real_norm_metric_space hNX.
pose P:= hom_of_linear p; pose J:= hom_of_linear j.
pose V:= p @` T.
have hpj:cancel J P:=(orthogonal_iff_adjoint_left_inverse hBZ hp).1 hj.
have hprojection:is_orthogonal_projection (@euclidean_inner_product R n)
    (@euclidean_inner_product R mu) p by exists j.
have hP v:NZ (P v)<=NX v:= orthogonal_projection_norm_bound hBX hBZ hprojection v.
have hPb:norm_bounded_linear NX NZ P.
  exists 1; split; first exact: ler01.
  by move=>v; rewrite mul1r; exact: hP.
have hJ:= norm_differential_bounded hBase.
have hbT:= norm_domain_interior_member hNX hTb.
have hpsib:psi (P b)= b:= hinv b hb hbT.
have [D hD]:=(norm_class_firstP hNZ hNX V psi).1 (norm_class_lower hk hpsi).
pose G:= fun z=>J z-psi z+(b-J (P b)).
have hG z:G z= J z-psi z+(b-J (P b)) by [].
have hGc:= @graph_defect_class R Z X NZ NX hNZ hNX V psi G J b (P b) k hG hJ hpsi.
have hTan:= projected_graph_tangent hb hTb hBase hrange hcan hinv.
pose u:=@AnnularCutoff.value R X _ hBX n (@coordinate_basis R n) (@coordinate_basisP R n) t ht.
pose C:=@AnnularCutoff.bound R X _ hBX n (@coordinate_basis R n) (@coordinate_basisP R n) t ht.
have hu:=@AnnularCutoff.laws R X _ hBX n (@coordinate_basis R n) (@coordinate_basisP R n) t ht.
have hC:0<C:= annular_cutoff_bound_positive hu.
have hCp:0<C+1 by lra.
pose eps:=(1-t)/(C+1).
have heps:0<eps by rewrite /eps divr_gt0 //; have :=(andP ht).2; lra.
have hepsC:eps*(C+1)= 1-t by rewrite /eps divfK // gt_eqF.
have [delta [hd hsmall]]:=@graph_defect_small R X Z NX NZ hNX hNZ V psi G P J D b eps
  hG hD hBase hpsib hP heps.
have [r0 [hr0 hBallT]]:= hTb.
pose rho:= Num.min r0 delta.
have hrho:0<rho by rewrite /rho lt_min hr0 hd.
exists rho; split; first exact hrho.
move=>r hr hrrho.
have /andP [hrr0 hrdelta]:(r<r0)&&(r<delta) by rewrite -lt_min.
pose U:= fun x=>V (P x).
pose W:= fun x=>G (P x).
have hWc:norm_class hNX hNX U W k:= @norm_class_precompose_linear R X Z X NX NZ NX hNX hNZ hNX V G P k hPb hGc.
pose K:set M:= fun x=>NX (x-b)<=r.
have hK:compact K:=@finite_norm_closed_ball_compact R X n
  (@coordinate_basis R n) (@coordinate_basisP R n) NX hNX b r.
have hKclosed:@closed M K:= compact_closed (@metric_hausdorff R M) hK.
have hKU x (hx:K x):U x.
  exact (hsmall x (le_trans hx (ltW hrdelta))).1.
have hKT x (hx:K x):T x.
  have hh:= hBallT (x-b) (le_lt_trans hx hrr0); by rewrite addrC subrK in hh.
have [w hw]:=@scaled_annular_cutoff_exists R X NX hNX t u C b r hu hr.
pose F:= fun x=>x+w x*:W x.
have hF x:F x= x+w x*:W x by [].
have [hFc hFix]:=@cutoff_graph_correction_class R X NX hNX U b t r w C W F k
  hw hWc hKclosed hKU hF.
have hWd x (hx:U x):has_norm_differential NX NX U W x
    (hom_comp (J-D (P x)) P).
  have hgd:= graph_defect_differential hNZ hNX hG hJ
    (norm_class_one_differential hD hx).
  have hpd:=@norm_differential_linear R X Z NX NZ hNX hNZ setT x P
    (norm_full_domain_interior NX x) hPb.
  have hc:= norm_differential_chain hNX hNZ hNX hpd hgd.
  have hUi:norm_domain_interior NX U x:=
    (@norm_class_continuous R X X NX NX hNX hNX U W k hWc x hx).1.
  exact (@norm_differential_restrict R X X NX NX (fun x=>True /\ V (P x)) U W x
    (hom_comp (J-D (P x)) P) (fun z hz=>conj Logic.I hz) hUi hc).
have hWB x (hx:NX (x-b)<=r):NX (W x)<=eps*NX (x-b) /\
    exists L:Hom X X,has_norm_differential NX NX U W x L /\
      forall v,NX (L v)<=eps*NX v.
  have [hxU [hmass hder]]:= hsmall x (le_trans hx (ltW hrdelta)).
  split; first exact hmass.
  exists (hom_comp (J-D (P x)) P); split; first exact (hWd x hxU).
  exact hder.
have hBound:=@cutoff_graph_correction_differential_bound R X NX hNX U b t r w C W F eps
  hw hr (ltW hC) (ltW heps) hKclosed hWB hF.
have [DF hDF]:=(norm_class_firstP hNX hNX setT F).1 (norm_class_lower hk hFc).
have hDfSmall a v:NX (DF a v-v)<=(1-t)*NX v.
  have hh:= hBound a (DF a) (norm_class_one_differential hDF Logic.I) v.
  by rewrite hepsC in hh.
have hc:0<=1-t<1 by have [ht0 ht1]:= andP ht; apply/andP; split; lra.
have hFixK x (hx:~K x):F x= x.
  apply: hFix; apply: ltW; rewrite ltNge; apply/negP=>hle; exact (hx hle).
have [g [hDif [hLipF hLipG]]]:=@euclidean_supported_small_diffeomorphism R n k F DF (1-t) K
  hc hFc hDF hDfSmall hK hFixK.
exists F,g; constructor; first exact hDif.
- move=>x y; apply: le_trans (hLipF x y) _.
  apply: ler_wpM2r; first exact (real_seminorm_nonnegative hNX.1 (x-y)).
  have ht0:0<t:=(andP ht).1.
  have hsquare:=sqr_ge0 (1-t).
  rewrite -div1r ler_pdivlMr //; nra.
- move=>x y; have he:1-(1-t)= t by ring.
  by rewrite he in hLipG; exact: hLipG.
- exact hFix.
- move=>x hx.
  have htr:t*r<r by have ht1:=(andP ht).2; nra.
  have hxK:K x:= ltW (lt_trans hx htr).
  have hw1:w x= 1:= scaled_cutoff_inner hw (ltW hx).
  have hFx:F x= x+G (P x) by rewrite /F hw1 scale1r.
  rewrite hTan.
  exact (@graph_correction_plane_equivalence R X Z B T V P J psi G F b x
    hpj (hKU x hxK) (hKT x hxK) hcan (fun z hz=>(hrange z hz).1) hinv hG hFx).
Qed.
