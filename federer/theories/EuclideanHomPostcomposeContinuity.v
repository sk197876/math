(** Federer (1969), 3.2.21, p. 257: supporting continuity
    of a restricted exterior power as the orthogonal coordinates vary. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  NormDifferentialUP NormMetric HomSpaceNormTopology EuclideanHomOperator NormFiniteLinearBound
  NormBoundedLinearTopology EuclideanLinearJacobian EuclideanJacobianContinuity
  EuclideanSliceJacobianRepresentative RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hom_postcompose_continuous]: supporting
    choice of g in O(m) in Federer 3.2.21, p. 257.
    Composition with a fixed differential is linear and continuous
    between the finite-dimensional spaces of operators. *)
Lemma euclidean_hom_postcompose_continuous (R:realType) k m n
    (D:Hom (R_n R m) (R_n R n)):
  continuous (fun A:real_norm_metric_space (@euclidean_operator_norm_is_norm R k m)=>
    (hom_comp D A:real_norm_metric_space (@euclidean_operator_norm_is_norm R k n))).
Proof.
pose NX:=@euclidean_operator_norm R k m.
pose NY:=@euclidean_operator_norm R k n.
pose hNX:=@euclidean_operator_norm_is_norm R k m.
pose hNY:=@euclidean_operator_norm_is_norm R k n.
have [q [b hb]]:=@hom_space_finite_basis R (R_n R k) (R_n R m)
  k (@coordinate_basis R k) (@coordinate_basisP R k)
  m (@coordinate_basis R m) (@coordinate_basisP R m).
pose A:=@HomMap R (Hom (R_n R k) (R_n R m)) (Hom (R_n R k) (R_n R n))
  (fun A=>hom_comp D A) (introT (asboolP _) (hom_postcompose_linear D)).
have hBound:norm_bounded_linear NX NY A:=norm_finite_linear_bounded hNX hNY hb A.
exact (@norm_bounded_linear_continuous R (Hom (R_n R k) (R_n R m))
  (Hom (R_n R k) (R_n R n)) NX NY hNX hNY A hBound).
Qed.

(** Source for [euclidean_restricted_jacobian_coordinates_continuous]:
    the nonzero exterior-power condition used to choose orthogonal
    coordinates in Federer 3.2.21, p. 257, is open.
    The fixed injection may be any coordinate block. *)
Lemma euclidean_restricted_jacobian_coordinates_continuous (R:realType) m n k
    (D:Hom (R_n R m) (R_n R n)) (j:Hom (R_n R k) (R_n R m)):
  continuous (fun A:real_norm_metric_space (@euclidean_operator_norm_is_norm R m m)=>
    (euclidean_linear_jacobian k (hom_comp D (hom_comp A j)):real_line_metric R)).
Proof.
move=>A; exact (continuous_comp (@euclidean_hom_precompose_continuous R m m k j A)
  (continuous_comp (@euclidean_hom_postcompose_continuous R k m n D (hom_comp A j))
    (@euclidean_top_jacobian_continuous R k n (hom_comp D (hom_comp A j))))).
Qed.
