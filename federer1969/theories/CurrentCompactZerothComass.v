(** Federer (1969), 4.1.12, pp. 367–368: an
    original unit-comass test has order-zero compact
    seminorm at most one. Use the exact derivative
    supremum and the preceding pointwise comass law,
    including empty compact sets and empty domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothFunctionSeminormFamily SmoothDerivativeSeminormUP
  SmoothTestSpaces CurrentGlobalComassSealed CurrentGlobalComassBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCompactZerothComass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (@current_test_value R h2 n U hU m).

(** Source for [current_compact_zeroth_comass_bound]: a
    nonnegative global comass bound also bounds the
    original nu_K^0, supporting the mass comparison in
    Federer 4.1.12, pp. 367–368. Nonnegativity of
    the proposed bound retains the empty-K convention. *)
Theorem current_compact_zeroth_comass_bound (phi:E) b:
  0<=b->(@CurrentGlobalComass.value R h2 n m U (ev phi)<=b%:E)%E->nu K 0%N phi<=b.
Proof.
move=>hb hGlobal.
have hPoint:=(@current_global_comass_bound R h2 n m U (ev phi) b).1 hGlobal.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K 0%N
  (nu K 0%N) (smooth_function_derivative_seminorm_laws hD K 0%N) phi b hb).
move=>j hj x hx.
have /eqP->:j==0%N by rewrite -leqn0.
rewrite (@smooth_derivative_zero_norm R X Y NX NY hNX hNY U E ev D hD
  phi x (smooth_compact_in_domain K x hx)).
exact:hPoint x (smooth_compact_in_domain K x hx).
Qed.

(** Source for [current_unit_test_compact_zeroth]: every
    original test admissible in the current mass has
    nu_K^0 at most one, supporting the joint mass
    estimate of Federer 4.1.12, pp. 367–368. *)
Lemma current_unit_test_compact_zeroth (phi:DT):
  (@CurrentGlobalComass.value R h2 n m U (value phi)<=1)%E->nu K 0%N (inc phi)<=1.
Proof.
move=>hGlobal.
exact:(@current_compact_zeroth_comass_bound (inc phi) (1:R) ler01 hGlobal).
Qed.
End CurrentCompactZerothComass.
