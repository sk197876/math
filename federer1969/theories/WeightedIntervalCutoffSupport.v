(** Federer (1969), 4.1.12, p. 369:
    the original cutoff supports lie
    in disjoint consecutive intervals. Thus
    only one cutoff can contribute
    at each scalar source point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry
  WeightedIntervalEndpoints WeightedIntervalCutoffUP WeightedIntervalCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalCutoffSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation support := (@current_test_support R h2 1%N 0%N Full hFull).

(** Source for [weighted_interval_cutoff_support_unique]:
    a source point cannot lie in
    the supports of two distinct
    original phi_k, supporting both printed
    psi_m estimates in Federer 4.1.12,
    p. 369. *)
Theorem weighted_interval_cutoff_support_unique x i j:
  support (phi i) x->support (phi j) x->i=j.
Proof.
move=>hi hj.
have hI:=(@WeightedIntervalCutoff.laws R h2 i).1 x hi.
have hJ:=(@WeightedIntervalCutoff.laws R h2 j).1 x hj.
have[hILow hIHigh]:=andP hI.
have[hJLow hJHigh]:=andP hJ.
case:(ltngtP i j)=>[hIJ|hJI|hEqual];last exact:hEqual.
- have h:=@weighted_interval_left_endpoint_monotone R i.+1 j hIJ.
  exfalso;lra.
- have h:=@weighted_interval_left_endpoint_monotone R j.+1 i hJI.
  exfalso;lra.
Qed.
End WeightedIntervalCutoffSupport.
