(** Federer (1969), 3.4.12, p. 339:
    the original unitary group is closed inside the
    actual compact orthogonal group. Apply the existing
    evaluation continuity and proved bounded complex scalar maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexScalarRealBounded HermitianUP HermitianRealImaginary HermitianComplexNorm
  InnerNorm InnerMetric HilbertFormCompactness LinearBasis HomInner LinearGroupTopology
  LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  NormMetric RealMetricBackground NormBoundedLinearTopology AnalyticOrthogonalJointContinuity
  PointwiseCommutingLocusUP PointwiseCommutingLocusSealed PointwiseCommutingClosed UnitaryGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Closed.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation XT:=(real_norm_metric_space hNX).
Variable N:nat.
Variable e:'I_N->XR.
Variable he:is_basis e.
Local Notation O:=(@orthogonal_group R XR B hB N e he).
Local Notation action:=(fun g:O=>@orthogonal_element_map R XR B hB N e he g).

(** Source for [unitary_group_closed]: closedness of
    the original scalar-commuting isometry group in 3.4.12,
    p. 339. Every actual scalar equation
    is a closed continuous equalizer. *)
Theorem unitary_group_closed:closed (@unitary_group R X H hH N e he).
Proof.
apply:(@pointwise_commuting_closed O XT (ComplexScalars.C R) action
  (fun (c:ComplexScalars.C R) (x:XT)=>c*:(x:X))
  (@unitary_group R X H hH N e he)
  (@PointwiseCommutingLocus.laws O X (ComplexScalars.C R) action
    (fun (c:ComplexScalars.C R) (x:X)=>c*:x))
  (@metric_hausdorff R XT)
  (@orthogonal_germ_fixed_vector_continuous R XR B hB N e he)).
move=>c.
have [M [hValues hBound]]:=@complex_scalar_real_bounded_exists R X NX
  (@hermitian_complex_norm R X H hH) c.
have hContinuous:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX M hBound.
have hSame:(fun x:XT=>c*:(x:X))=(fun x:XT=>M x).
  apply:funext=>x;exact:esym (hValues x).
by rewrite hSame.
Qed.
End Closed.
