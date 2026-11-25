(** Federer (1969), 3.4.2(7), p. 314: the local cutting
    manifold through a noncommon critical point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm InnerConvex HilbertFormCompactness RealNormUP NormMetric
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal NormClassOneUP
  NormRegularity NormRegularityOperations NormOpenPreimage NormOpenDomainLaws
  NormLinearDomainLaws NormBoundedLinearTopology NormDiffeomorphismUP
  EuclideanProjectionSpace OrthogonalInjectionSpaces EuclideanRectangularAdjoint
  StructureProjectionDistance CriticalManifoldFamilyUP CriticalChartRetractionClass
  CriticalLineKernelProjection CriticalCompositeKernel CriticalJointLocalDiffeomorphism
  CriticalJointZeroSlice CriticalProjectionSectionFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_scalar_cutting_chart]: the construction
    of V in Ω(mu-1,k) in 3.4.2(7), p. 314. The scalar map has
    a nonzero derivative on p(z). Choose the printed kernel line,
    invert the joint map locally, and restrict its inverse to the
    scalar-zero slice. The resulting manifold lies in any prescribed
    open neighbourhood of a, and its intersection with C contains
    a neighbourhood of a relative to C. The zero-dimensional
    cutting manifold is included by the same projection-section laws. *)
Theorem critical_scalar_cutting_chart (R:realType) m d
    (Z:G (R_n R m) d) gamma k (S C O:set (R_n R m))
    (p:euclidean_projection_space R m gamma.+1) g
    (F:R_n R gamma.+1->R) (D:Hom (R_n R gamma.+1) R^o) a z:
  (1<=k)%N ->(m-d<=gamma)%N ->
  is_critical_manifold_chart k (grassmann_val Z) S p g ->
  C `<=` S ->C a ->grassmann_val Z z ->
  @open (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) O ->O a ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R gamma.+1))
    (@scalar_absolute_value_norm R) (euclidean_projection_linear p @` S) F k ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R gamma.+1))
    (fun t:R^o=>`|t|) (euclidean_projection_linear p @` S) F
    (euclidean_projection_linear p a) D ->D (euclidean_projection_linear p z)!=0 ->
  (forall c,C c ->F (euclidean_projection_linear p c)=0) ->
  exists V:set (R_n R m),critical_manifold_family Z gamma k V /\
    V `<=` S /\V `<=` O /\exists N:set (R_n R m),
      @open (real_norm_metric_space
        (inner_norm_real_norm (@euclidean_inner_productP R m))) N /\
      N a /\C `&` N `<=` V.
Proof.
move=>hk hDimension hChart hCS hc hz hO haO hF hD hNonzero hCZero.
pose X:=R_n R m;pose Y:=R_n R gamma.+1;pose W:=R_n R gamma.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R gamma.+1).
pose NW:=inner_norm (@euclidean_inner_productP R gamma).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R gamma.+1).
pose hNW:=inner_norm_real_norm (@euclidean_inner_productP R gamma).
pose P:=hom_of_linear (euclidean_projection_linear p).
pose U:=euclidean_projection_linear p @` S.
pose v:=P z.
have ha:S a:=hCS a hc.
have haU:U (P a) by exists a.
have hV:v!=0.
  apply/eqP=>hv.
  have hZeroP:euclidean_projection_linear p z=0:=hv.
  by rewrite hZeroP linear0 eqxx in hNonzero.
have [q hKernel]:=critical_line_kernel_projection_exists hV.
pose Q:=hom_of_linear (euclidean_projection_linear q).
pose J:=@euclidean_rectangular_adjoint R gamma.+1 gamma
  (@orthogonal_projection_map R W Y (@euclidean_inner_product R gamma)
    (@euclidean_inner_product R gamma.+1) (@euclidean_inner_productP R gamma)
    (@euclidean_inner_productP R gamma.+1) gamma.+1 (@coordinate_basis R gamma.+1)
    (@coordinate_basisP R gamma.+1) q).
have hSection:cancel J Q.
  move=>u;exact:(@structure_projection_adjoint_cancel R gamma.+1 gamma q u).
have hQv:Q v=0.
  apply:(hKernel v).2;exists 1;by rewrite scale1r.
have hKernelQ w (hw:Q w=0):exists t:R,w=t*:v:= (hKernel w).1 hw.
pose A:=fun w=>U w /\O (g w).
have hAOpen:@open (real_norm_metric_space hNY) A.
  exact:(@norm_class_zero_open_preimage R Y X NY NX hNY hNX U O g
    (norm_class_continuous (critical_chart_inverse_class hChart)) hO).
have hAInterior w (hw:A w):norm_domain_interior NY A w.
  exact:(proj2 (@norm_domain_interior_neighbourhood R Y NY hNY A w)
    (open_nbhs_nbhs (conj hAOpen hw))).
have haA:A (P a).
  split;first exact:haU.
  by rewrite (critical_chart_left_inverse hChart ha).
have hFA:=@norm_class_open_restriction R Y R^o NY (fun t:R^o=>`|t|)
  hNY (@scalar_absolute_value_norm R) U A F k (fun w hw=>hw.1) hAInterior hF.
have hDA:=@norm_differential_restrict R Y R^o NY (fun t:R^o=>`|t|) U A F (P a) D
  (fun w hw=>hw.1) (hAInterior (P a) haA) hD.
have [r [hr [hInside [h hLocal]]]]:=@critical_joint_local_diffeomorphism R gamma.+1 k W
  Q J A F D (P a) v hk hFA haA hDA hSection hQv hV hNonzero hKernelQ.
pose B:=fun w=>NY (w-P a)<r.
pose G:=fun w=>J (Q w)+F w*:v.
have haB:B (P a) by rewrite /B subrr /NY inner_norm0.
have hFa:F (P a)=0:=hCZero a hc.
have [rho [hRho [hSliceClass [hSlice hSliceLeft]]]]:=
  @critical_joint_zero_slice R gamma.+1 gamma k Q J F v B (G @` B) h (P a)
    hSection hQv hV haB hFa hLocal.
pose V0:=fun u=>NW (u-Q (P a))<rho.
pose psi:=fun u=>g (h (J u)).
have hParameter u (hu:V0 u):U (h (J u)).
  exact:(hInside (h (J u)) (hSlice u hu).1).1.
have hPsiClass:norm_class hNW hNX V0 psi k.
  exact:(norm_class_compose_on hParameter hSliceClass (critical_chart_inverse_class hChart)).
have [projection [hProjection hProjectionKernel]]:=
  @critical_composite_projection_kernel R m gamma.+1 gamma k (grassmann_val Z) S p g q z
    hChart hz hKernelQ.
have hCancel u (hu:V0 u):euclidean_projection_linear projection (psi u)=u.
  rewrite hProjection /psi (critical_chart_right_inverse hChart (hParameter u hu)).2.
  exact:(hSlice u hu).2.1.
have hConvex:is_inner_convex V0:=@norm_open_ball_convex R W NW hNW (Q (P a)) rho.
have hFamily:=@critical_projection_section_family R m d Z gamma k projection V0 psi
  hDimension hk hProjectionKernel hConvex hPsiClass hCancel.
exists (psi @` V0);split;first exact:hFamily.
split.
- move=>x [u hu <-];exact:(critical_chart_right_inverse hChart (hParameter u hu)).1.
split.
- move=>x [u hu <-];exact:(hInside (h (J u)) (hSlice u hu).1).2.
pose N:=fun x=>B (P x) /\V0 (euclidean_projection_linear projection x).
exists N;split.
- rewrite openE=>x hx.
  apply:(proj1 (@norm_domain_interior_neighbourhood R X NX hNX N x)).
  apply:norm_domain_intersection_interior.
  + exact:(@norm_bounded_linear_preimage_interior R X Y NX NY hNX P B x
      (critical_projection_bounded_linear p)
      (@norm_open_ball_domain_interior R Y NY hNY (P a) r (P x) hx.1)).
  + exact:(@norm_bounded_linear_preimage_interior R X W NX NW hNX
      (hom_of_linear (euclidean_projection_linear projection)) V0 x
      (critical_projection_bounded_linear projection)
      (@norm_open_ball_domain_interior R W NW hNW (Q (P a)) rho
        (euclidean_projection_linear projection x) hx.2)).
split.
- split;first exact:haB.
  by rewrite /V0 hProjection subrr /NW inner_norm0.
- move=>x [hcx [hxB hxV]].
  have hParam:V0 (Q (P x)) by move:hxV;rewrite hProjection.
  exists (Q (P x));first exact:hParam.
  rewrite /psi (hSliceLeft (P x) hxB (hCZero x hcx) hParam).
  exact:(critical_chart_left_inverse hChart (hCS x hcx)).
Qed.
