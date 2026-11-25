(** Federer (1969), 4.1.8, p. 362,
    used in 4.1.12, pp. 368–369:
    the actual scalar segment boundary
    acts by its original endpoint difference.
    Reuse the proved Dirac boundary identity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentPointEvaluation CurrentBoundary CurrentDirac OrientedSegmentCurrentSealed
  OrientedSegmentCurrentBoundary ScalarSegmentCoordinateValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_segment_boundary_value]: every
    original zero-form test sees its
    right endpoint value minus its left
    endpoint value on the actual segment
    boundary, supporting Federer 4.1.12,
    pp. 368–369. Reversed and
    degenerate endpoints are retained. *)
Theorem scalar_segment_boundary_value (R:realType) (h2:(1+1:R)!=0) (u v:R)
    (psi:@current_test_space R h2 1%N (fun _=>True)
      (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 0%N):
  @current_value R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 0%N
    (@current_boundary R h2 1%N 0%N (fun _=>True)
      (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x)
      (@OrientedSegmentCurrent.value R h2 1%N (fun _=>True)
        (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x)
        (euclidean_one_embed u) (euclidean_one_embed v) (@scalar_segment_full_domain R u v))) psi=
  zero_form_value (@current_test_value R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 0%N psi (euclidean_one_embed v))-
  zero_form_value (@current_test_value R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 0%N psi (euclidean_one_embed u)).
Proof.
rewrite oriented_segment_current_boundary.
pose hFull:=fun (x:R_n R 1%N) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x.
pose E:=@current_point_evaluation R h2 1%N 0%N (fun _=>True) hFull psi.
change (E (@dirac_current R h2 1%N (fun _=>True) hFull (euclidean_one_embed v)-
    @dirac_current R h2 1%N (fun _=>True) hFull (euclidean_one_embed u))=
    zero_form_value (@current_test_value R h2 1%N (fun _=>True) hFull 0%N psi (euclidean_one_embed v))-
    zero_form_value (@current_test_value R h2 1%N (fun _=>True) hFull 0%N psi (euclidean_one_embed u))).
rewrite (linB (hom_linear E)) /E !current_point_evaluation_values.
by rewrite !dirac_current_evaluation.
Qed.
