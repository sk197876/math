(** Federer (1969), 4.1.27, p. 384:
    a globally Lipschitz representative equal to
    the original polynomial near the closed
    cube has the same actual flat
    image. Reuse support agreement from 4.1.15,
    p. 372, followed by the original
    smooth-image agreement on the compact cube current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormRegularity InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP LipschitzBasic
  NormLocalLipschitzScalarProduct SmoothCompactSet CurrentSpaces CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzSupportAgreement CurrentFlatSmoothPushforward
  EuclideanOpenUnitCube CurrentCharacteristicSupportClosure
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeParametrisationClass SimplexCubeSourceCurrent SimplexCubeCurrentImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_representative_current_image]: the actual
    image needed to apply 4.1.25 to
    the cube in 4.1.27, p. 384.
    The representative need only be globally
    Lipschitz and equal on the closed
    cube; it need not be smooth
    outside the original compact source. *)
Theorem simplex_cube_representative_current_image (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n) (G:R_n R m->R_n R n)
    (hLip:@is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R n)) setT G):
  (forall x,smooth_compact_carrier (@simplex_cube_source_index R m) x->
    G x=@SimplexCubeParametrisation.value R n m v x)->
  @CurrentFlatLipschitzPushforward.value R h2 m n m (fun _=>True) (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) x)
    (fun y (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) y)
    G (fun _ _=>Logic.I)
    (@metric_lipschitz_is_local R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) setT G hLip)
    (@simplex_cube_source_current R h2 m) (@simplex_cube_source_current_flat R h2 m)=
      @simplex_cube_current_image R h2 n m v.
Proof.
move=>hAgreement.
pose X:=R_n R m;pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose FullX:=fun _:X=>True;pose FullY:=fun _:Y=>True.
pose hFullX:=fun (x:X) (_:True)=>norm_full_domain_interior NX x.
pose hFullY:=fun (y:Y) (_:True)=>norm_full_domain_interior NY y.
pose T:=@simplex_cube_source_current R h2 m.
pose hT:=@simplex_cube_source_current_flat R h2 m.
pose hCompact:=@simplex_cube_source_current_compact R h2 m.
pose F:=@SimplexCubeParametrisation.value R n m v.
pose hSmooth:=@simplex_cube_parametrisation_smooth R n m v.
pose hImage:=fun (x:X) (_:True)=>Logic.I.
pose hLocalG:=@metric_lipschitz_is_local R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) setT G hLip.
have hFirst:norm_class_one NX NY FullX F:=
  (@norm_class_firstP R X Y NX NY hNX hNY FullX F).1 (hSmooth 1%N).
pose hLocalF:=@norm_class_one_locally_metric_lipschitz R X Y NX NY hNX hNY FullX F hFirst.
have hOnSupport:forall x,@current_support R h2 m FullX hFullX m T x->G x=F x.
  move=>x hx;apply:hAgreement.
  exact:(@euclidean_characteristic_current_support_closure R h2 m
    (@euclidean_open_unit_cube R m) (@simplex_cube_source_measurable R m) x hx).
have hCompare:=@current_flat_lipschitz_support_agreement R h2 m n m
  FullX FullY hFullX hFullY G F hImage hImage hLocalG hLocalF T hT hOnSupport.
pose hProper:=@current_compact_map_proper R h2 m n m FullX FullY hFullX T F hImage
  (norm_class_continuous (hSmooth 0%N)) hCompact.
have hSmoothImage:=@current_flat_lipschitz_pushforward_smooth R h2 m n m
  FullX FullY hFullX hFullY F hImage hLocalF T hT hSmooth hProper.
exact:eq_trans hCompare hSmoothImage.
Qed.
