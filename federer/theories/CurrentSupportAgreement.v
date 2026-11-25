(** Federer (1969), 4.1.7, pp. 357–359:
    agreement of currents near a point is
    expressed by exclusion from the support
    of their difference. These supporting
    equivalences use the original local-annihilation
    definition from 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import NormBoundedLinearTopology Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormOpenTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentSupportGeometry FunctionalSupportUP SmoothTestFunctionalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSupportAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation support := (@current_test_support R h2 n m U hU).
Local Notation csupport := (@current_support R h2 n U hU m).

(** Source for [current_test_disjoint_support_zero]:
    a current annihilates every original test
    with disjoint support, supporting the
    constancy, locality and pushforward statements
    of Federer 4.1.7, pp. 357–359,
    by the proved 4.1.1 support theorem. *)
Theorem current_test_disjoint_support_zero (T:C) (psi:DT):
  (forall x,csupport T x->~support psi x)->action T psi=0.
Proof.
exact:(@smooth_test_functional_disjoint_support_zero R X (A_m X R^o m) NX
  (@current_form_comass R h2 n m) hNX (@current_form_comass_real_norm R h2 n m) n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU
  (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m)
  (@current_smooth_space_laws R h2 n U hU m) (action T) psi).
Qed.

(** Source for [current_support_difference_agreement]:
    agreement on tests supported in open A
    puts the difference support in U minus
    A, supporting the constancy and normality
    assertions of Federer 4.1.7, pp. 357–358. *)
Theorem current_support_difference_agreement (T S:C) (A:set X):
  @open XT A ->(forall psi:DT,support psi `<=` A->action T psi=action S psi) ->
  csupport (T-S) `<=` (U `&` ~` A).
Proof.
move=>hA hAgree x [hx hNot];split=>// hxA.
apply:hNot;exists A;split;last exact:hxA.
split;first exact:hA.
move=>psi hPsi;rewrite linearB.
change (action T psi-action S psi=0).
by rewrite (hAgree psi hPsi) subrr.
Qed.

(** Source for [current_agreement_near_point]: a
    point of U outside spt(T-S) has
    an open neighbourhood on which every
    supported test has equal action, supporting
    Federer 4.1.7, p. 358. *)
Theorem current_agreement_near_point (T S:C) x:
  U x->~csupport (T-S) x ->
  exists W:set X,@open XT W /\ W x /\ W `<=` U /\
    forall psi:DT,support psi `<=` W->action T psi=action S psi.
Proof.
move=>hx hOutside.
have hSome:exists W,smooth_functional_annihilation_open hNX U
    (@current_test_value R h2 n U hU m) (action (T-S)) W /\ W x.
  apply:contrapT=>hNone;apply:hOutside;by split.
have[W [[hW hZero] hxW]]:=hSome.
have hOpenU:@open XT U.
  rewrite openE=>z hz;exact:(@norm_domain_interior_neighbourhood R X NX hNX U z).1 (@hU z hz).
exists (W `&` U);split;first exact:openI hW hOpenU.
split;first by split.
split;first by move=>z [_ hz].
move=>psi hPsi.
have h:=hZero psi (fun z hz=>(hPsi z hz).1).
rewrite linearB in h.
change (action T psi-action S psi=0) in h.
apply/eqP;rewrite -subr_eq0;exact/eqP.
Qed.
End CurrentSupportAgreement.
