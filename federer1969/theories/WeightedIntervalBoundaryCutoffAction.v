(** Federer (1969), 4.1.12, p. 369:
    the actual original T=boundary S
    satisfies T(phi_k)=k. The original
    endpoint values make every sufficiently
    long finite boundary prefix have
    precisely that value. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentBoundary CurrentWeakLimitOperations WeightedIntervalEndpoints WeightedIntervalCurrentUP WeightedIntervalCurrentSealed
  WeightedIntervalCurrentLaws WeightedIntervalBoundaryPrefix WeightedIntervalCutoffSealed WeightedIntervalCutoffValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalBoundaryCutoffAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation S := (@WeightedIntervalCurrent.value R h2).
Local Notation T := (@weighted_interval_boundary R h2).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation B := (@current_boundary R h2 1%N 0%N Full hFull).
Local Notation action := (@current_value R h2 1%N Full hFull 0%N).
Local Notation prefix := (@weighted_interval_current_prefix R h2).

(** Source for [weighted_interval_boundary_cutoff_action]:
    each actual original phi_k has
    T(phi_k)=k, with no extra
    representation premise on T, Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_boundary_cutoff_action n:action T (phi n)=(n.+1)%:R.
Proof.
have hPrefix L:(n.+1<=L)%N->action (B (prefix L)) (phi n)=(n.+1)%:R.
  move=>hNL;rewrite weighted_interval_boundary_prefix_value.
  have hTerms j:(j.+1)%:R*(zero_form_value
      (@current_test_value R h2 1%N Full hFull 0%N (phi n)
        (euclidean_one_embed (weighted_interval_right_endpoint R j)))-
      zero_form_value (@current_test_value R h2 1%N Full hFull 0%N (phi n)
        (euclidean_one_embed (weighted_interval_left_endpoint R j))))=
      (if j==n then (n.+1)%:R else 0).
    rewrite weighted_interval_cutoff_right_value weighted_interval_cutoff_left_value zero_formK
      (linear0 (@zero_form_value R X R^o)) subr0.
    case:(eqVneq j n)=>hJN;first by subst j;rewrite mulr1.
    by rewrite mulr0.
  have hSum: \sum_(j<L) (j.+1)%:R*(zero_form_value
      (@current_test_value R h2 1%N Full hFull 0%N (phi n)
        (euclidean_one_embed (weighted_interval_right_endpoint R j)))-
      zero_form_value (@current_test_value R h2 1%N Full hFull 0%N (phi n)
        (euclidean_one_embed (weighted_interval_left_endpoint R j))))=
      \sum_(j<L) (if val j==n then (n.+1)%:R else 0).
    apply:eq_bigr=>j _;exact:hTerms j.
  rewrite hSum.
  have hIndex:(n<L)%N:=hNL.
  rewrite (bigD1 (@Ordinal L n hIndex)) //= eqxx.
  have hRest: \sum_(j<L|j!=(@Ordinal L n hIndex)) (if val j==n then ((n.+1)%:R:R) else 0)=0.
    apply:big1=>j hj.
    have hNeq:(val j!=n)%N.
      by move:hj;rewrite -val_eqE.
    by rewrite (negPf hNeq).
  by rewrite hRest addr0.
have hWeak:=@current_weak_limit_boundary R h2 1%N 0%N Full hFull prefix S
  (@WeightedIntervalCurrent.laws R h2).
exact:(@current_weak_limit_eventual_value R h2 1%N 0%N Full hFull
  (fun k=>B (prefix k)) T (phi n) (n.+1)%:R n.+1 hWeak hPrefix).
Qed.
End WeightedIntervalBoundaryCutoffAction.
