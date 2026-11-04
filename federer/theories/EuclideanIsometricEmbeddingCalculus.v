(** Federer (1969), 3.2.47, p. 283: supporting
    submanifold structure of the actual isotropy from its
    isometry with O(n-1). An actual isometric injection
    between Euclidean ambient spaces is affine by 3.2.36,
    p. 273. Its open constant-rank restriction gives the
    submanifold image by 3.1.19(3), p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  OrthogonalMaps AdjointCriteria EuclideanRectangularAdjoint
  MetricIsometricInjectionAffine NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormClassOneUP NormClassOneActualField
  NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormFiniteLinearBound NormOpenDomainLaws NormClassZeroTopology NormMetric
  LinearInjectiveRank EuclideanSubmanifoldUP SubmanifoldOpenImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_isometric_embedding_calculus]: actual
    isometric injections are affine and smooth, with their
    actual constant differential and a continuous left inverse;
    supporting the manifold images of 3.2.47, p. 283,
    by 3.2.36, p. 273, and 3.1.1, p. 210. *)
Theorem euclidean_isometric_embedding_calculus (R:realType) m n
    (F:R_n R m->R_n R n):
  (forall x y,mdist (F x:inner_metric_space (@euclidean_inner_productP R n)) (F y)=
    mdist (x:inner_metric_space (@euclidean_inner_productP R m)) y) ->
  exists L:Hom (R_n R m) (R_n R n),
    is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear L) /\
    norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT F /\
    is_norm_class_one_field (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT F (fun _=>L) /\
    exists G:R_n R n->R_n R m,cancel F G /\
      continuous (fun y:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))=>
        (G y:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))).
Proof.
move=>hMetric.
pose X:=R_n R m.
pose Y:=R_n R n.
pose hX:=@euclidean_inner_productP R m.
pose hY:=@euclidean_inner_productP R n.
pose NX:=inner_norm hX.
pose NY:=inner_norm hY.
pose hNX:=inner_norm_real_norm hX.
pose hNY:=inner_norm_real_norm hY.
have [hLinear hPair]:=@metric_isometric_injection_linear_part R X Y _ _ hX hY F hMetric.
pose L:Hom X Y:=@HomMap R X Y (fun x=>F x-F 0) (introT (asboolP _) hLinear).
have hL:is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear L):=hPair.
have hLBound:norm_bounded_linear NX NY L.
  exists 1; split; first exact:ler01.
  move=>x.
  have hNorm:NY (L x)=NX x:=@orthogonal_map_norm R X Y _ _ hX hY (hom_as_linear L) hL x.
  by rewrite hNorm mul1r.
have hFormula:F=fun x=>F 0+L x.
  apply:funext=>x; change (F x=F 0+(F x-F 0)).
  by rewrite addrC subrK.
have hSmooth:norm_class_all_orders hNX hNY setT F.
  rewrite hFormula=>j; apply:norm_class_add.
  - exact:(@norm_class_constant R X Y NX NY hNX hNY setT (F 0) j
      (fun x _=>@norm_full_domain_interior R X NX x)).
  - exact:(@norm_class_linear R X Y NX NY hNX hNY setT L j
      (fun x _=>@norm_full_domain_interior R X NX x) hLBound).
have hDifferential x:has_norm_differential NX NY setT F x L.
  have hConstant:=@norm_differential_constant R X Y NX NY hNX hNY setT x (F 0)
    (@norm_full_domain_interior R X NX x).
  have hLinearDifferential:=@norm_differential_linear R X Y NX NY hNX hNY setT x L
    (@norm_full_domain_interior R X NX x) hLBound.
  have hSum:=norm_differential_add hNY hConstant hLinearDifferential.
  rewrite add0r in hSum.
  by rewrite hFormula.
have hField:is_norm_class_one_field NX NY setT F (fun _=>L).
  apply:(@norm_class_one_actual_field R X Y NX NY hNX hNY setT F (fun _=>L)).
  - exact:((@norm_class_firstP R X Y NX NY hNX hNY setT F).1 (hSmooth 1%N)).
  - by move=>x _; exact:hDifferential x.
pose J:=euclidean_rectangular_adjoint L.
have hJBound:norm_bounded_linear NY NX J.
  exact (@norm_finite_linear_bounded R Y X NY NX hNY hNX n
    (@coordinate_basis R n) (@coordinate_basisP R n) J).
have hLeft:cancel L J.
  exact ((orthogonal_iff_adjoint_left_inverse hX (euclidean_rectangular_adjoint_pairing L)).1 hL).
pose G:=fun y:Y=>J (y-F 0).
have hGClass:norm_class hNY hNX setT G 0%N.
  apply:(@norm_class_postcompose_linear R Y Y X NY NY NX hNY hNY hNX setT
    (fun y:Y=>y-F 0) J 0%N hJBound).
  apply:norm_class_subtract.
  - apply:(@norm_class_linear R Y Y NY NY hNY hNY setT (hom_of_linear (linear_id Y)) 0%N).
    + by move=>y _; exact:norm_full_domain_interior.
    + exists 1; split; first exact:ler01.
      by move=>y; rewrite mul1r.
  - exact:(@norm_class_constant R Y Y NY NY hNY hNY setT (F 0) 0%N
      (fun y _=>@norm_full_domain_interior R Y NY y)).
have hGContinuous:continuous (fun y:real_norm_metric_space hNY=>(G y:real_norm_metric_space hNX)).
  move=>y; exact:(@norm_class_zero_continuous_at R Y X NY NX hNY hNX setT G y
    (norm_class_continuous hGClass) I).
have hGF:cancel F G.
  move=>x; rewrite /G (congr1 (fun f=>f x) hFormula) addrC addKr.
  exact:hLeft x.
exists L; split; first exact hL.
split; first exact hSmooth.
split; first exact hField.
exists G; by split.
Qed.
