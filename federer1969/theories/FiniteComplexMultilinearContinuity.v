(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: finitely many complex basis-tuple values detect the
    original real operator-norm topology. Reuse the proved paired
    coordinate injection and finite norm comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  ComplexCoefficientAlgebra ComplexScalarCoordinateBounds NormBoundedLinearTopology LinearBasis FiniteCoordinates
  InnerProductUP InnerNorm HilbertFormCompactness InnerMetric EuclideanInnerProduct FiniteNormEquivalence
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  FiniteComplexMultilinearCoordinates EuclideanCoordinateTopology FiniteLinearContinuityReflection ScalarNormExtendedEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_complex_multilinear_continuous_from_basis_values]:
    the original finite derivative coordinate criterion, 3.4.12,
    p. 339. Zero-dimensional sources and order zero remain. *)
Theorem finite_complex_multilinear_continuous_from_basis_values
    (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (b:'I_n->X) (hb:is_basis b) m (P:topologicalType)
    (f:P->@ContinuousMultilinear.space R m X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)):
  (forall l:{ffun 'I_m->'I_n},continuous (fun p:P=>
    (@ContinuousMultilinear.evaluation R m X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) [ffun i=>b (l i)] (f p):
      real_norm_metric_space (@complex_modulus_real_norm R)))) ->
  continuous (fun p:P=>(f p:real_norm_metric_space
    (continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
      (@ContinuousMultilinear.laws R m X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
        NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))))).
Proof.
move=>hValues.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose N:=@complex_modulus R;pose hN:=@complex_modulus_real_norm R.
pose Z:=@ContinuousMultilinear.space R m X CR NX N hNX hN.
pose NZ:=@ContinuousMultilinear.norm R m X CR NX N hNX hN.
pose hNZ:=continuous_multilinear_norm_is_norm hN (@ContinuousMultilinear.laws R m X CR NX N hNX hN).
pose L:=@finite_complex_multilinear_coordinate_hom R X NX hNX n b m.
have hL:=@finite_complex_multilinear_coordinate_injective R X NX hNX n b hb m.
pose d:=#|[the finType of ({ffun 'I_m->'I_n}*bool)%type]|.
pose NY:=inner_norm (@euclidean_inner_productP R d).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R d).
have hRe:continuous (fun z:real_norm_metric_space hN=>(ComplexScalars.re z:real_norm_metric_space (@scalar_absolute_value_norm R))).
  exact:(@norm_bounded_linear_continuous R CR R^o N (fun r:R^o=>`|r|) hN (@scalar_absolute_value_norm R) _ (@complex_real_part_bounded R)).
have hIm:continuous (fun z:real_norm_metric_space hN=>(ComplexScalars.im z:real_norm_metric_space (@scalar_absolute_value_norm R))).
  exact:(@norm_bounded_linear_continuous R CR R^o N (fun r:R^o=>`|r|) hN (@scalar_absolute_value_norm R) _ (@complex_imaginary_part_bounded R)).
have hScalar:continuous (fun r:real_norm_metric_space (@scalar_absolute_value_norm R)=>(r:R^o)).
  exact:(@scalar_norm_real_identity_continuous R).
have hReal:continuous (fun z:real_norm_metric_space hN=>(ComplexScalars.re z:R^o)).
  move=>z;exact:(continuous_comp (hRe z) (hScalar _)).
have hImaginary:continuous (fun z:real_norm_metric_space hN=>(ComplexScalars.im z:R^o)).
  move=>z;exact:(continuous_comp (hIm z) (hScalar _)).
have hCoordinates:continuous (fun p:P=>(L (f p):inner_metric_space (@euclidean_inner_productP R d))).
  apply:euclidean_map_continuous=>i.
  have hEq:(fun p:P=>(L (f p) i:R^o))=
    (fun p:P=>if (enum_val i).2 then ComplexScalars.im
      (@ContinuousMultilinear.evaluation R m X CR NX N hNX hN [ffun j=>b ((enum_val i).1 j)] (f p))
    else ComplexScalars.re
      (@ContinuousMultilinear.evaluation R m X CR NX N hNX hN [ffun j=>b ((enum_val i).1 j)] (f p))).
    by apply:funext=>p;rewrite /L /finite_complex_multilinear_coordinate_hom /= /finite_complex_multilinear_coordinate_map ffunE.
  rewrite hEq;case hCase:(enum_val i).2=>p.
  - exact:(continuous_comp (hValues (enum_val i).1 p) (hImaginary _)).
  - exact:(continuous_comp (hValues (enum_val i).1 p) (hReal _)).
have hMap:continuous (fun p:P=>(L (f p):real_norm_metric_space hNY)).
  move=>p U hU;apply:hCoordinates.
  exact:(proj2 (@inner_real_norm_same_nbhs R _ _ (@euclidean_inner_productP R d) (L (f p)) U) hU).
have [q [e [he hDimension]]]:=@finite_complex_multilinear_basis_exists R X NX hNX n b hb m.
exact:(@finite_injective_linear_continuity_reflection R Z (coordinate_space R d)
  NZ NY hNZ hNY q e he L hL P f hMap).
Qed.
