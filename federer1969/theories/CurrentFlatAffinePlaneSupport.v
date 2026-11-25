(** Federer (1969), 4.1.15, p. 373: no nonzero flat
    m-current has support in an (m-1)-dimensional affine plane.
    Enlarge the original open target to its ambient space,
    use the preceding Lipschitz-section set equality, and
    restrict back. The original arbitrary open U is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AffineMaps AffineSubspaceSpace AffinePlaneLipschitzSection EuclideanAffineSmooth
  LipschitzUP NormLocalLipschitzScalarProduct CurrentSpaces FlatCurrentsUP
  CurrentOpenIdentitySmooth CurrentOpenRestriction CurrentFlatLipschitzSection
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzTargetNeighbourhood CurrentFlatIdentityPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_affine_plane_support_zero]: a flat
    m-current supported in an affine d-plane vanishes whenever
    d<m, the slightly stronger dimensional form of Federer
    4.1.15, p. 373. No assumption of compactness, finite mass
    or normality is added to original flat membership. *)
Theorem current_flat_affine_plane_support_zero (R : realType)
    (h2 : (1+1:R)!=0) n d m (hDegree : (d<m)%N)
    (U : set (R_n R n))
    (hU : forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (A : set (R_n R n))
    (hA : @is_affine_subspace_dim R (R_n R n) d A)
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current R h2 n m U hU T)
    (hSupport : @current_support R h2 n U hU m T `<=` A) :
  T=0.
Proof.
pose X:=R_n R n;pose Y:=R_n R d.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R d).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose FullX:set X:=setT;pose FullY:set Y:=setT.
pose hFullX:=fun x (_:FullX x)=>@norm_full_domain_interior R X NX x.
pose hFullY:=fun y (_:FullY y)=>@norm_full_domain_interior R Y NY y.
pose hIdImage:=fun x (hx:U x)=>hx.
pose hAmbientImage:=fun (x:X) (_:U x)=>Logic.I.
pose hIdClass:=@current_open_identity_smooth R n U hU.
pose hIdLocal:=@norm_class_one_locally_metric_lipschitz R X X NX NX hNX hNX
  U (fun x=>x) ((@norm_class_firstP R X X NX NX hNX hNX U
    (fun x=>x)).1 (hIdClass 1%N)).
pose Q:=@CurrentFlatLipschitzPushforward.value R h2 n n m U FullX hU hFullX
  (fun x=>x) hAmbientImage hIdLocal T hFlat.
pose hQ:=proj1 (@CurrentFlatLipschitzPushforward.laws R h2 n n m
  U FullX hU hFullX (fun x=>x) hAmbientImage hIdLocal T hFlat).
have hQA:@current_support R h2 n FullX hFullX m Q `<=` A.
  move=>y hy.
  have [x hx <-]:=@current_flat_lipschitz_pushforward_support R h2 n n m
    U FullX hU hFullX (fun x=>x) hAmbientImage hIdLocal T hFlat y hy.
  exact:(@hSupport x hx).
have [f [g [hF [hG [hCancel hRange]]]]]:=
  @affine_plane_lipschitz_section_exists R n d A hA.
pose hFImage:=fun (y:Y) (_:FullY y)=>Logic.I.
pose hGImage:=fun (x:X) (_:FullX x)=>Logic.I.
pose hFClass:=@euclidean_affine_map_smooth R d n FullY hFullY f hF.
pose hGClass:=@euclidean_affine_map_smooth R n d FullX hFullX g hG.
pose hFLocal:=@norm_class_one_locally_metric_lipschitz R Y X NY NX hNY hNX
  FullY f ((@norm_class_firstP R Y X NY NX hNY hNX FullY f).1
    (hFClass 1%N)).
pose hGLocal:=@norm_class_one_locally_metric_lipschitz R X Y NX NY hNX hNY
  FullX g ((@norm_class_firstP R X Y NX NY hNX hNY FullX g).1
    (hGClass 1%N)).
have hSectionSupport:@current_support R h2 n FullX hFullX m Q `<=` f @` FullY.
  move=>x hx;have [y hy]:=(hRange x).2 (@hQA x hx).
  exists y;first exact:Logic.I.
  exact:hy.
have hQZero:=@current_flat_lipschitz_section_above_dimension R h2 d n m
  FullY FullX hFullY hFullX f g hFImage hGImage hFLocal hGLocal
  (fun y (_:FullY y)=>hCancel y) hDegree Q hQ hSectionSupport.
have hRestriction:=@current_flat_lipschitz_target_neighbourhood_restriction
  R h2 n n m U U FullX hU hU hFullX (fun x=>x)
  hIdImage hAmbientImage hAmbientImage hIdLocal T hFlat.
have hIdentity:=@current_flat_lipschitz_identity_pushforward R h2 n m
  U hU hIdImage hIdLocal T hFlat.
apply:(eq_trans (esym hIdentity)).
apply:(eq_trans (esym hRestriction)).
change (@current_open_restriction R h2 n m U FullX hU hFullX hAmbientImage Q=0).
by rewrite hQZero linear0.
Qed.

(** Source for [current_flat_affine_plane_successor_support_zero]:
    the exact positive-degree assertion printed in Federer
    4.1.15, p. 373, with m=d+1 and an arbitrary d-plane. *)
Corollary current_flat_affine_plane_successor_support_zero (R : realType)
    (h2 : (1+1:R)!=0) n d
    (U : set (R_n R n))
    (hU : forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (A : set (R_n R n))
    (hA : @is_affine_subspace_dim R (R_n R n) d A)
    (T : @current_space R h2 n U hU d.+1)
    (hFlat : @is_flat_current R h2 n d.+1 U hU T)
    (hSupport : @current_support R h2 n U hU d.+1 T `<=` A) :
  T=0.
Proof.
exact:(@current_flat_affine_plane_support_zero R h2 n d d.+1
  (ltnSn d) U hU A hA T hFlat hSupport).
Qed.

Arguments current_flat_affine_plane_support_zero : clear implicits.
Arguments current_flat_affine_plane_successor_support_zero : clear implicits.
