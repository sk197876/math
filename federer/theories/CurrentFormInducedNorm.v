(** Federer (1969), 4.1.7, pp. 355–357: the
    actual comass-normed real forms carry the induced
    norm used in 4.1.6. Degree zero retains the
    proved absolute-scalar convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct AlternatingForms
  AlternatingZero AlternatingFormNormUP AlternatingFormZeroNorm EuclideanFormNorm
  Comass CurrentCoefficientNorms ZeroDegreeCovectorNorm ComassInducedNormEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFormInducedNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation V := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation NX := (inner_norm hB).
Local Notation hNX := (inner_norm_real_norm hB).
Local Notation e := (@coordinate_basis R n).
Local Notation he := (@coordinate_basisP R n).
Local Notation P := (fun m=>@euclidean_form_norm R h2 n R^o
  (fun c:R^o=>`|c|) (@scalar_absolute_value_norm R) m).
Local Notation hP := (fun m=>@euclidean_form_norm_laws R h2 n R^o
  (fun c:R^o=>`|c|) (@scalar_absolute_value_norm R) m).

(** Source for [current_form_comass_induced_equal]:
    equality of the actual original real-form norms,
    supporting Federer 4.1.7, pp. 355–357. *)
Theorem current_form_comass_induced_equal m (phi:A_m V R^o m):
  @current_form_comass R h2 n m phi = P m phi.
Proof.
case:m phi=>[phi|p phi].
- rewrite /current_form_comass (@zeroth_covector_absolute_norm R h2 V B hB n e he phi).
  symmetry; exact:(@alternating_form_zero_norm R V R^o NX (fun c:R^o=>`|c|)
    hNX (@scalar_absolute_value_norm R) (P 0%N) (hP 0%N) phi).
- exact:(@positive_comass_induced_norm R h2 V B hB p.+1 (ltn0Sn p)
    (P p.+1) (hP p.+1) phi _ (@comassP R h2 V B hB n e he p.+1 (ltn0Sn p) phi)).
Qed.

(** Source for [current_form_comass_is_induced]: the
    actual coefficient norm satisfies the original
    induced-norm specification required by 4.1.6,
    supporting Federer 4.1.7, pp. 355–357. *)
Theorem current_form_comass_is_induced m:
  is_alternating_form_norm NX (fun c:R^o=>`|c|) (@current_form_comass R h2 n m).
Proof.
move=>phi; rewrite current_form_comass_induced_equal; exact:(hP m phi).
Qed.
End CurrentFormInducedNorm.
