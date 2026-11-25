(** Federer (1969), 3.4.8(5), p. 328:
    finitely many original basis-tuple evaluations detect
    continuity of scalar derivative forms in their exact
    operator norm. Finite norm comparison supplies the inverse
    estimate; no coordinate inverse is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis FiniteCoordinates
  InnerProductUP InnerNorm HilbertFormCompactness InnerMetric EuclideanInnerProduct FiniteNormEquivalence
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  FiniteMultilinearCoordinates EuclideanCoordinateTopology FiniteLinearContinuityReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_multilinear_continuous_from_basis_values]:
    the finite-coordinate continuity criterion for the actual
    derivatives used in 3.4.8(5), p. 328.
    All derivative orders and zero source dimension remain. *)
Theorem finite_multilinear_continuous_from_basis_values
    (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (b:'I_n->X) (hb:is_basis b) m (P:topologicalType)
    (f:P->@ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|) hNX
      (@scalar_absolute_value_norm R)):
  (forall l:{ffun 'I_m->'I_n},continuous (fun p:P=>
    (@ContinuousMultilinear.evaluation R m X R^o NX (fun t=>`|t|) hNX
      (@scalar_absolute_value_norm R) [ffun i=>b (l i)] (f p):R^o))) ->
  continuous (fun p:P=>(f p:real_norm_metric_space
    (continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
      (@ContinuousMultilinear.laws R m X R^o NX (fun t=>`|t|) hNX
        (@scalar_absolute_value_norm R))))).
Proof.
move=>hValues.
pose Z:=@ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R).
pose NZ:=@ContinuousMultilinear.norm R m X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R).
pose hNZ:=continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)).
pose L:=@finite_multilinear_coordinate_hom R X NX hNX n b m.
have hL:=@finite_multilinear_coordinate_injective R X NX hNX n b hb m.
pose d:=#|{ffun 'I_m->'I_n}|.
pose NY:=inner_norm (@euclidean_inner_productP R d).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R d).
have hCoordinates:continuous (fun p:P=>(L (f p):inner_metric_space (@euclidean_inner_productP R d))).
  apply:euclidean_map_continuous=>i.
  have hEq:(fun p:P=>(L (f p) i:R^o))=
      (fun p:P=>(@ContinuousMultilinear.evaluation R m X R^o NX (fun t=>`|t|)
        hNX (@scalar_absolute_value_norm R) [ffun j=>b ((enum_val i) j)] (f p):R^o)).
    by apply:funext=>p;rewrite /L /finite_multilinear_coordinate_hom /=
      /finite_multilinear_coordinate_map ffunE.
  rewrite hEq;exact:(hValues (enum_val i)).
have hMap:continuous (fun p:P=>(L (f p):real_norm_metric_space hNY)).
  move=>p U hU;apply:hCoordinates.
  exact:(proj2 (@inner_real_norm_same_nbhs R _ _ (@euclidean_inner_productP R d) (L (f p)) U) hU).
have [q [e [he hDimension]]]:=@finite_scalar_multilinear_basis_exists R X NX hNX n b hb m.
exact:(@finite_injective_linear_continuity_reflection R Z (coordinate_space R d)
  NZ NY hNZ hNY q e he L hL P f hMap).
Qed.
