(** Federer (1969), 3.4.4, p. 318: the
    constant polynomial jets used in the application of 3.1.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Graded GradedSums GradedDegree SymmetricForms SymmetricFormZero
  SymmetricFormSum HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation
  SymmetricPolynomialInjectivity PolynomialDiagonalNorm PolynomialFunctions PolynomialRepresentations
  PolynomialTaylor PolynomialTaylorTransform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [flat_whitney_constant_polynomial_exists]:
    P_a(x)=phi(a), 3.4.4, p. 318.
    Prove existence of an actual degree-zero polynomial with
    exactly the prescribed zero-order coefficient and vanishing
    positive Taylor coefficients at every point. Its homogeneous
    representation is an existence proof, not an added premise. *)
Theorem flat_whitney_constant_polynomial_exists (R:realType)
    (X Y:lmodType R) (y:Y):
  exists P:PolynomialFunction X Y,
    (forall x,P x=y) /\polynomial_degree P=0%N /\
    (forall x,polynomial_taylor_coefficient P 0 x=zero_sform X y) /\
    forall i x,polynomial_taylor_coefficient P i.+1 x=0.
Proof.
pose F:=sform_include (zero_sform X y).
pose P:=polynomial_from_forms F.
have hValue x:symmetric_polynomial_value F x=y.
  by rewrite /F symmetric_polynomial_value_include sform_polynomial_diagonal_value
    zero_sformE fact0 invr1 scale1r.
have hBound:grade_bounded (S_star_grading X Y) F 1.
  move=>i hi;rewrite /F sform_include_grade.
  have hNe:i!=0%N by rewrite -lt0n;exact:hi.
  by rewrite (negPf hNe).
have hDegree:(polynomial_degree P<=0)%N.
  rewrite /P (polynomial_degree_from_forms (@pchar_num R)).
  exact:graded_degree_le_of_bound hBound.
have hDegreeZero:polynomial_degree P=0%N.
  apply/eqP;by move:hDegree;rewrite leqn0.
have hTranslation x:symmetric_taylor_transform F x=F.
  apply:(symmetric_polynomial_injective (@pchar_num R));apply:funext=>v.
  by rewrite (symmetric_taylor_transform_value (@pchar_num R)) !hValue.
exists P;split;first exact:hValue.
split=>//;split.
- move=>x;by rewrite /polynomial_taylor_coefficient /P
    (polynomial_from_formsK (@pchar_num R)) hTranslation /F sform_includeK.
- move=>i x;rewrite /polynomial_taylor_coefficient /P
    (polynomial_from_formsK (@pchar_num R)) hTranslation.
  apply:(can_inj (@sform_includeK R X Y i.+1)).
  by rewrite linear0 sform_componentK /F sform_include_grade.
Qed.
