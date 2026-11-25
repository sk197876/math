(** Federer (1969), 3.2.48, p. 285: the actual full ambient
    polynomial differential of Psi, specified by its printed values.
    The existing differential existence theorem identifies this linear
    formula; it is not an assumed derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm EuclideanHomInnerCharts EuclideanRectangularAdjoint ProductInner
  ProductInnerNormBounds HomCompositionDeterminant NormDifferentialUP OrthogonalKinematicMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_differential]: the actual
    ambient formula D Psi(x,y)(u,v)=u y adjoint+x v adjoint, supporting
    the original inverse formula in 3.2.48, p. 285. *)
Definition orthogonal_kinematic_differential (R:realType) N
    (x y:Hom (R_n R N) (R_n R N)):=
  hom_comp (hom_of_linear (@hom_right_composition R (R_n R N) (R_n R N) (euclidean_rectangular_adjoint y)))
    (@product_first_projection_hom R (Hom (R_n R N) (R_n R N)) (Hom (R_n R N) (R_n R N)))+
  hom_comp (hom_of_linear (@hom_left_composition R (R_n R N) (R_n R N) x))
    (hom_comp (hom_of_linear (GRing.Linear.clone _ _ _ _ (@euclidean_rectangular_adjoint R N N) _))
      (@product_second_projection_hom R (Hom (R_n R N) (R_n R N)) (Hom (R_n R N) (R_n R N)))).

(** Source for [orthogonal_kinematic_differentialE]: the original
    derivative values from 3.2.48, p. 285, with the actual adjoint
    polynomial extension on the full ambient Cartesian space. *)
Lemma orthogonal_kinematic_differentialE (R:realType) N
    (x y u v:Hom (R_n R N) (R_n R N)):
  orthogonal_kinematic_differential x y (u,v)=
    hom_comp u (euclidean_rectangular_adjoint y)+hom_comp x (euclidean_rectangular_adjoint v).
Proof. by []. Qed.

(** Source for [orthogonal_kinematic_differential_actual]: the actual
    full-domain differential used for the Jacobian in 3.2.48, p. 285.
    Its existence is proved by the polynomial calculus, with no supplied
    differential or independent derivative-field hypothesis. *)
Theorem orthogonal_kinematic_differential_actual (R:realType) N
    (x y:Hom (R_n R N) (R_n R N)):
  has_norm_differential
    (inner_norm (product_inner_productP
      (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)))
    (inner_norm (@euclidean_hom_inner_productP R N N))
    setT (@orthogonal_kinematic_map R N) (x,y) (orthogonal_kinematic_differential x y).
Proof.
have [D [hD hValue]]:=@orthogonal_kinematic_map_differential R N x y.
have hSame:D=orthogonal_kinematic_differential x y.
  apply:hom_ext=>z; case:z=>u v; by rewrite hValue orthogonal_kinematic_differentialE.
by rewrite -hSame.
Qed.
