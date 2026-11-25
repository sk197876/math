(** Federer (1969), 3.4.2(7), p. 314: the inverse of the
    cutting projection parametrises an admissible smaller manifold. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP InnerConvex
  NormDifferentialUP NormClassZeroTopology NormRegularity NormRegularityOperations NormLinearDomainLaws
  EuclideanSubmanifoldUP SubmanifoldChartsUP SubmanifoldCoordinateParametrisation
  SubmanifoldParametrisationStraightening EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalChartRetractionClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_projection_section_family]: the assertion
    V belongs to Ω(mu-1,k) in 3.4.2(7), p. 314. A class-k
    section over a convex open projection image is a submanifold
    by 3.1.19. The projection and section supply the original
    chart laws, and the kernel remains in Z. Zero-dimensional
    parameter spaces are included. *)
Theorem critical_projection_section_family (R:realType) m d
    (Z:G (R_n R m) d) gamma k (p:euclidean_projection_space R m gamma)
    (W:set (R_n R gamma)) (psi:R_n R gamma->R_n R m):
  (m-d<=gamma)%N ->(1<=k)%N ->
  (forall x,euclidean_projection_linear p x=0 ->grassmann_val Z x) ->
  is_inner_convex W ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R gamma))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) W psi k ->
  (forall u,W u ->euclidean_projection_linear p (psi u)=u) ->
  critical_manifold_family Z gamma k (psi @` W).
Proof.
move=>hDimension hk hKernel hConvex hPsi hCancel.
pose X:=R_n R m;pose V:=R_n R gamma.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NV:=inner_norm (@euclidean_inner_productP R gamma).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R gamma).
pose P:=hom_of_linear (euclidean_projection_linear p).
pose B:=psi @` W.
pose T:=fun x=>W (P x).
have hPBound:=critical_projection_bounded_linear p.
have hWinterior u (hu:W u):norm_domain_interior NV W u:=(norm_class_continuous hPsi hu).1.
have hTInterior x (hx:T x):norm_domain_interior NX T x.
  exact:(@norm_bounded_linear_preimage_interior R X V NX NV hNX P W x
    hPBound (hWinterior (P x) hx)).
have hPClass:=@norm_class_linear R X V NX NV hNX hNV T P k hTInterior hPBound.
have hBT:B `<=` T.
  move=>x [u hu <-];by rewrite /T /P hom_of_linearE (hCancel u hu).
have hImage:euclidean_projection_linear p @` B=W.
  apply/seteqP;split.
  - move=>u [x [v hv <-] <-];by rewrite (hCancel v hv).
  - move=>u hu;exists (psi u);first by exists u.
    exact:hCancel u hu.
have hImageT:psi @` W=B `&` T.
  apply/seteqP;split;[by move=>x hx;split;last exact:hBT x hx|by move=>x [hx _]].
have hCoordinates:@has_convex_coordinate_charts R m gamma k B.
  move=>b hb;exists T,W,(euclidean_projection_linear p),psi.
  split;first exact:(hTInterior b (hBT b hb)).
  split;first exact:hConvex.
  split;first exact:hPClass.
  split;first exact:hPsi.
  split;first by move=>x.
  split;first by move=>u hu;rewrite /T /P hom_of_linearE (hCancel u hu).
  split;[exact:hImageT|exact:hCancel].
have hManifold:=open_parametrisations_submanifold hk
  (convex_coordinates_open_parametrisations hk hCoordinates).
split;first exact:hDimension.
split;first exact:hk.
split;first exact:hManifold.
right;exists p,psi;constructor.
- exact:hKernel.
- by rewrite hImage.
- rewrite hImage;exact:(@norm_class_zero_domain_open R V X NV NX hNV W psi (norm_class_continuous hPsi)).
- by rewrite hImage.
- move=>x [u hu <-];by rewrite (hCancel u hu).
- move=>u hu;have huW:W u by rewrite -hImage.
  split;first by exists u.
  exact:hCancel u huW.
Qed.
