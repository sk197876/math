(** Federer (1969), 4.1.7, p. 355,
    used for the weighted tests of
    4.1.12, p. 369: scalar
    multiplication cannot enlarge an original
    test support. Use the actual
    pointwise scalar law and closure monotonicity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentSupportGeometry CurrentTestValueLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_test_scalar_support_subset]:
    the original support of c phi
    is contained in that of phi,
    supporting the disjoint weighted psi_m
    terms in Federer 4.1.12,
    p. 369. Zero c is included. *)
Lemma current_test_scalar_support_subset (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    c (phi:@current_test_space R h2 n U hU m):
  @current_test_support R h2 n m U hU (c*:phi) `<=`
    @current_test_support R h2 n m U hU phi.
Proof.
move=>x [hx hClosure];split;first exact:hx.
apply:(@closureS (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  [set y|@current_test_value R h2 n U hU m (c*:phi) y<>0]
  [set y|@current_test_value R h2 n U hU m phi y<>0] _ x hClosure).
move=>y hNonzero hZero;apply:hNonzero.
by rewrite current_test_scale_value hZero scaler0.
Qed.
