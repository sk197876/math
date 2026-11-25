(** Federer (1969), 4.1.7, p. 359: the
    original point evaluation delta_c on open
    U. Restriction from the whole Euclidean
    space preserves the actual scalar test
    values and yields the required current. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  CurrentCoefficientNorms CurrentDiracDensity CurrentOpenRestriction CurrentEvaluation SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentDirac.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.

(** Source for [dirac_current]: the original
    delta_c in D_0(U), supporting Federer
    4.1.7, p. 359. At points outside
    U its normalized evaluation is zero. *)
Definition dirac_current (c:X):@current_space R h2 n U hU 0%N:=
  @current_open_restriction R h2 n 0%N U (fun _=>True) hU hFull (fun _ _=>Logic.I)
    (@full_dirac_current R h2 n c).

(** Source for [dirac_current_evaluation]: delta_c(psi)
    equals the original scalar coefficient
    psi(c), Federer 4.1.7, p. 359. *)
Theorem dirac_current_evaluation c psi:
  @current_value R h2 n U hU 0%N (dirac_current c) psi=
    zero_form_value (@current_test_value R h2 n U hU 0%N psi c).
Proof.
rewrite /dirac_current current_open_restriction_evaluation full_dirac_current_evaluation
  current_open_test_extension_values;by [].
Qed.

(** Source for [dirac_current_outside]: restricting a
    point mass at c outside U gives
    the zero current, supporting the missing
    endpoint term on (0,infinity) in
    Federer 4.1.7, p. 359. *)
Theorem dirac_current_outside c:~U c->dirac_current c=0.
Proof.
move=>hc;apply:(@current_values_extensional R h2 n 0%N U hU)=>psi.
rewrite dirac_current_evaluation.
have hZero:@current_test_value R h2 n U hU 0%N psi c=0.
  exact:(@smooth_test_value_outside R X (A_m X R^o 0) NX (@current_form_comass R h2 n 0%N)
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (@current_form_comass_real_norm R h2 n 0%N)
    U (@current_smooth_space R h2 n U hU 0%N) (@current_smooth_value R h2 n U hU 0%N)
    (@current_smooth_space_laws R h2 n U hU 0%N) psi c hc).
by rewrite hZero !linear0 hom_zeroE.
Qed.
End CurrentDirac.

(** Source for [dirac_current_full_agreement]:
    the original point current on the
    whole Euclidean space agrees with its
    open-domain definition, supporting Federer 4.1.7,
    p. 359. Both are identified by
    their actual scalar test evaluations. *)
Theorem dirac_current_full_agreement (R:realType) (h2:(1+1:R)!=0) n (c:R_n R n):
  @dirac_current R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>
      @norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) c=
    @full_dirac_current R h2 n c.
Proof.
apply:(@current_values_extensional R h2 n 0%N (fun _=>True)
  (fun (x:R_n R n) (_:True)=>
    @norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x))=>psi.
by rewrite dirac_current_evaluation full_dirac_current_evaluation.
Qed.
