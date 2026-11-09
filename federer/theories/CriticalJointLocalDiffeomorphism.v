(** Federer (1969), 3.4.2(7), p. 314: the joint scalar and
    projection map gives a local class-k diffeomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialFiniteCalculus NormDifferentialDirectional
  NormClassOneUP NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormFiniteLinearBound NormHigherCurveDerivativeUP NormedPrimitiveCell
  NormDiffeomorphismUP FiniteLocalDiffeomorphism CriticalJointLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_joint_local_diffeomorphism]: the inverse
    function step for the map (F,q) in 3.4.2(7), p. 314.
    Write its target coordinates in the source space as
    j(q(w))+F(w)v. The proved injective differential permits the
    finite-dimensional inverse function theorem. Its neighbourhood,
    inverse, and inverse regularity are conclusions. *)
Theorem critical_joint_local_diffeomorphism (R:realType) n k
    (W:lmodType R) (q:Hom (R_n R n) W) (j:Hom W (R_n R n))
    (A:set (R_n R n)) (F:R_n R n->R) (D:Hom (R_n R n) R^o) a v:
  (1<=k)%N ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) A F k ->A a ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) A F a D ->
  cancel j q ->q v=0 ->v!=0 ->D v!=0 ->
  (forall w,q w=0 ->exists t:R,w=t*:v) ->
  exists radius:R,0<radius /\
    (forall x,inner_norm (@euclidean_inner_productP R n) (x-a)<radius ->A x) /\
    exists h:R_n R n->R_n R n,
      is_norm_diffeomorphism
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        [set x|inner_norm (@euclidean_inner_productP R n) (x-a)<radius]
        ((fun x=>j (q x)+F x*:v) @`
          [set x|inner_norm (@euclidean_inner_productP R n) (x-a)<radius])
        (fun x=>j (q x)+F x*:v) h k.
Proof.
move=>hk hF ha hD hSection hV hv hDv hKernel.
pose X:=R_n R n.
pose B:=@euclidean_inner_product R n.
pose hB:=@euclidean_inner_productP R n.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
pose P:=hom_comp j q.
pose V:=scalar_coefficient_linear_map v.
pose G:=fun x=>j (q x)+F x*:v.
have hInterior x (hx:A x):norm_domain_interior N A x:=(norm_class_continuous hF hx).1.
have hPBound:=@norm_finite_linear_bounded R X X N N hN hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) P.
have hVBound:=scalar_coefficient_linear_bound hN v.
have hPClass:=@norm_class_linear R X X N N hN hN A P k hInterior hPBound.
have hVClass:=@norm_class_postcompose_linear R X R^o X N (fun t:R^o=>`|t|) N
  hN (@scalar_absolute_value_norm R) hN A F V k hVBound hF.
have hG:norm_class hN hN A G k:=norm_class_add hPClass hVClass.
have hPActual:=@norm_differential_linear R X X N N hN hN A a P
  (hInterior a ha) hPBound.
have hVActual:=norm_differential_postcompose hN hD hVBound.
have hJoint:has_norm_differential N N A G a (critical_joint_linear_map q j D v):=
  norm_differential_add hN hPActual hVActual.
have [DG hDG]:=(norm_class_firstP hN hN A G).1 (norm_class_lower hk hG).
have hSame:DG a=critical_joint_linear_map q j D v:=norm_differential_unique hN hN
  (norm_class_one_differential hDG ha) hJoint.
have hInjective:injective (DG a).
  rewrite hSame;exact:(critical_joint_linear_injective hSection hV hv hDv hKernel).
exact:(@finite_local_diffeomorphism R X B hB hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) A G DG a k hG hDG ha hInjective).
Qed.
