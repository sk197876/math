(** Federer (1969), 4.1.12, p. 369:
    independent laws for the original phi_k
    on (u_k,u_(k+1)), with unit value
    at v_k and derivative bound k^3.
    Existence and opaque choice are separate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentSupportGeometry CurrentZeroCovectorMaps CurrentCoefficientNorms
  CurrentTestExteriorDerivative WeightedIntervalEndpoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section WeightedIntervalCutoffUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation DT := (@current_test_space R h2 1%N Full hFull 0%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).

(** Source for [is_weighted_interval_cutoff]: the
    original phi_k is supported inside
    (u_k,u_(k+1)), has values in
    [0,1], equals one at v_k
    and has derivative comass at most
    k^3, Federer 4.1.12, p. 369.
    Formal n denotes k=n+1. *)
Definition is_weighted_interval_cutoff n (phi:DT):Prop:=
  (@current_test_support R h2 1%N 0%N Full hFull phi `<=`
    [set x|weighted_interval_left_endpoint R n<euclidean_one_project x<weighted_interval_left_endpoint R n.+1]) /\
  (forall x,0<=@current_zero_form_coefficient R 1%N (value phi x)<=1) /\
  value phi (euclidean_one_embed (weighted_interval_right_endpoint R n))=@zero_form R X R^o 1 /\
  forall x,@current_form_comass R h2 1%N 1%N
    (@current_test_value R h2 1%N Full hFull 1%N
      (@current_test_exterior_derivative R h2 1%N 0%N Full hFull phi) x)<=((n.+1)%:R)^+3.

(** Source for [is_weighted_interval_cutoff_family]: one
    family has all the original printed
    phi_k laws, supporting Federer 4.1.12,
    p. 369. *)
Definition is_weighted_interval_cutoff_family (f:nat->DT):Prop:=
  forall n,is_weighted_interval_cutoff n (f n).
End WeightedIntervalCutoffUP.
