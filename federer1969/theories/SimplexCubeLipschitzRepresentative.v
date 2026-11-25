(** Federer (1969), 4.1.27, p. 384:
    apply the preceding global Lipschitz image
    theorem to a representative agreeing with
    the original polynomial near the closed
    cube. All needed global regularity is
    derived from the earlier compact plateau;
    no false global bound is imposed on the polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormRegularity GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness LipschitzUP SmoothCompactSet
  CurrentMapDifferential EuclideanOpenUnitCube
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeParametrisationClass SimplexCubeSourceCurrent
  ClassOneCompactGlobalLipschitzRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_lipschitz_representative_exists]: the
    supporting application of 4.1.25 to
    the original compact cube in 4.1.27,
    p. 384. The chosen representative agrees
    with the original map and its actual
    differential on one open neighbourhood of
    the entire closed cube, including m=0. *)
Theorem simplex_cube_lipschitz_representative_exists (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  exists G:R_n R m->R_n R n,exists W:set (R_n R m),
    @open (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) W /\
    smooth_compact_carrier (@simplex_cube_source_index R m) `<=` W /\
    @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R n)) setT G /\
    norm_class_one (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (fun _=>True) G /\
    (forall x,W x->G x=@SimplexCubeParametrisation.value R n m v x) /\
    forall x,W x->@current_map_differential R m n (fun _=>True) G x=
      @current_map_differential R m n (fun _=>True)
        (@SimplexCubeParametrisation.value R n m v) x.
Proof.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Full:=fun _:R_n R m=>True.
pose hFull:=fun (x:R_n R m) (_:True)=>norm_full_domain_interior NX x.
pose f:=@SimplexCubeParametrisation.value R n m v.
have hFirst:norm_class_one NX NY Full f:=
  (@norm_class_firstP R (R_n R m) (R_n R n) NX NY hNX hNY Full f).1
    (@simplex_cube_parametrisation_smooth R n m v 1%N).
have[G [W [hW [hKW [_ [hLip [hClass [hValues hDifferential]]]]]]]]:=
  @class_one_compact_global_lipschitz_representative R m n Full hFull
    (@simplex_cube_source_index R m) f hFirst.
exists G,W;split;first exact:hW.
split;first exact:hKW.
split;first exact:hLip.
split;first exact:hClass.
split;[exact:hValues|exact:hDifferential].
Qed.
