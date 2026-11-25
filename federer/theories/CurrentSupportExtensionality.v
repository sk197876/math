(** Federer (1969), 4.1.7, pp. 357–359:
    a current with empty support is zero.
    This is the original support annihilation
    law of 4.1.1, p. 345,
    applied to the actual compact tests. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import CurrentEvaluation Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet CurrentSpaces
  CurrentSupportGeometry CurrentSupportAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_empty_support_iff_zero]:
    empty original support is equivalent to
    the zero actual current, supporting constancy
    and the corrected primitive uniqueness in
    Federer 4.1.7, pp. 357–359. *)
Theorem current_empty_support_iff_zero (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  (@current_support R h2 n U hU m T `<=` set0)<->T=0.
Proof.
split.
- move=>hEmpty;apply:(@current_values_extensional R h2 n m U hU)=>psi.
  rewrite linear0 hom_zeroE.
  apply:current_test_disjoint_support_zero=>x hx _;exact:hEmpty x hx.
- move=>->.
  exact:(@current_support_zero_subset R h2 n m U hU
    (@smooth_compact_empty R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)).
Qed.
