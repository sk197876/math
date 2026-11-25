(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    the original polynomial equations bound the
    fibres over compact prefix sets. Apply
    the proved coefficient and coordinate bounds,
    then the existing finite basis expansion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import ComplexOrderedBases HolomorphicLinear NormFiniteLinearBound NormVectorEquationCompactFibre OriginalComplexPolynomialFibreNormBound ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexModulusInverse HolomorphicCoordinateNorm Hom TensorUP RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicCoordinateNormBounds NormDifferentialUP
  NormClassOneUP NormRegularity NormRegularityOperations NormOpenDomainLaws NormCompactFunctionBound
  NormAnalyticUP CompactAnalyticComplexCoefficientBounds OriginalComplexPolynomialCoordinateBounds
  FieldPrefixCoordinatesUP OrdinalCoordinateTail FieldPrefixSuffixSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactFibres.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:is_complex_norm NX.
Local Notation hNXR:=(complex_norm_real hNX).
Variables n m:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Hypothesis hMN:(m<=n)%N.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Variable P:Hom X Y.
Hypothesis hP:is_field_prefix_projection omega hMN P.
Variable first:'I_(n-m).
Variable k:nat.
Hypothesis hK:(0<k)%N.
Variables U C:set Y.
Variable delta:Y->ComplexScalars.C R.
Variable b0:'I_k->Y->ComplexScalars.C R.
Variable b:'I_(n-m)->'I_k->Y->ComplexScalars.C R.
Variable Z:set X.
Hypothesis hCompact:compact [set y:real_norm_metric_space hNY|C y].
Hypothesis hCU:C `<=` U.
Hypothesis hNonzero:forall y,C y ->delta y!=0.
Hypothesis hDelta:@norm_analytic R YR CR NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U delta.
Hypothesis hB0:forall i,@norm_analytic R YR CR NY (@complex_modulus R) hNY
  (@complex_modulus_real_norm R) U (b0 i).
Hypothesis hB:forall j i,@norm_analytic R YR CR NY (@complex_modulus R) hNY
  (@complex_modulus_real_norm R) U (b j i).
Hypothesis hRoot:forall x,Z x ->
  (omega (tail first) x)^+k+\sum_(i<k) b0 i (P x)*(omega (tail first) x)^+(i:nat) = 0.
Hypothesis hRelations:forall x,Z x ->forall j,j!=first ->
  delta (P x)*omega (tail j) x = \sum_(i<k) b j i (P x)*(omega (tail first) x)^+(i:nat).

Variable f:'I_(n-m)->X->ComplexScalars.C R.
Hypothesis hF:forall j,@norm_class_zero R
  (restricted_space (ComplexScalars.embed R) X) CR NX (@complex_modulus R)
  (fun x=>U (P x)) (f j).
Hypothesis hZ:forall x,Z x <->U (P x) /\(forall j,f j x=0) /\delta (P x)<>0.

(** Source for [original_complex_polynomial_compact_fibres]:
    compactness of the original polynomial zero system over
    every compact prefix set away from delta zero, 3.4.12,
    p. 339, extending 3.4.8(10), p. 332. The original monic
    equation proves boundedness. Existing vector common-zero closedness
    and finite-dimensional compact balls finish the argument. *)
Theorem original_complex_polynomial_compact_fibres:
  compact [set x:real_norm_metric_space hNXR|Z x /\C (P x)].
Proof.
have [M [hM hBound]]:=@original_complex_polynomial_fibre_norm_bound R X NX hNX n m e he omega hDual
  hMN P hP first k hK U C delta b0 b Z hCompact hCU hNonzero hDelta hB0 hB hRoot hRelations.
pose XR:=restricted_space (ComplexScalars.embed R) X.
have hPBound:=@norm_finite_linear_bounded R XR YR NX NY hNXR hNY
  (n+n) (ordered_real_basis e) (ordered_real_basisP he) (complex_hom_real P).
apply:(@norm_vector_equation_compact_fibre R XR YR CR NX NY (@complex_modulus R)
  hNXR hNY (@complex_modulus_real_norm R) (n+n) (ordered_real_basis e)
  (ordered_real_basisP he) (complex_hom_real P) U C 'I_(n-m) f Z
  hPBound hCompact hCU hF _ _).
- move=>x hc;split.
  + move=>hz;exact:((hZ x).1 hz).2.1.
  + move=>hZero;apply:(hZ x).2;split;first exact:hCU (P x) hc.
    split;first exact:hZero;apply/eqP;exact:hNonzero (P x) hc.
- by exists M.
Qed.
End CompactFibres.
