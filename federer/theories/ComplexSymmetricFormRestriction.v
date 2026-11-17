(** Federer (1969), 3.4.12, pp. 338–339:
    original complex symmetric forms are real symmetric
    forms on the underlying spaces. This is the
    missing scalar-restriction connection to the existing homogeneous
    series theorem of 3.1.24, pp. 238–239. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import ScalarRestriction ComplexScalarSealed AlternatingForms
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Restriction.
Variable R:realFieldType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variable m:nat.

(** Source for [complex_symmetric_form_real_exists]: the
    original complex form has a real symmetric-form
    carrier with exactly the original tuple values,
    supporting 3.4.12, pp. 338–339. *)
Theorem complex_symmetric_form_real_exists (F:S_m X Y m):
  exists G:S_m XR YR m,forall t,G t=F t.
Proof.
have hLinear:@m_linear R XR YR m (fun t=>F t).
  move=>s t h a x y.
  have hContext (v:X):@context_tuple R XR m s t h v=
      @context_tuple C X m s t h v by apply:val_inj.
  rewrite !hContext.
  change (F (@context_tuple C X m s t h (ComplexScalars.embed R a*:(x:X)+y))=
    ComplexScalars.embed R a*:(F (@context_tuple C X m s t h x):Y)+
    F (@context_tuple C X m s t h y)).
  exact:(@sform_multilinear C X Y m F s t h (ComplexScalars.embed R a) x y).
have hSymmetric:@tuple_symmetric R XR YR m (fun t=>F t).
  exact:sform_tuple_symmetric F.
have hLaws:@sform_pred R XR YR m (fun t=>F t).
  apply/asboolP;by split.
exists (@SymmetricForm R XR YR m (fun t=>F t) hLaws);by move=>t.
Qed.

(** Source for [complex_homogeneous_polynomial_real]: every
    original complex homogeneous polynomial is a real homogeneous
    polynomial of the same degree, 3.4.12,
    pp. 338–339. Exact factorial normalization is preserved,
    including degree zero. *)
Theorem complex_homogeneous_polynomial_real (P:X->Y):
  @is_homogeneous_polynomial C X Y m P ->
  @is_homogeneous_polynomial R XR YR m P.
Proof.
move=>[F hF];have [G hG]:=complex_symmetric_form_real_exists F.
exists G=>x;rewrite hF !sform_polynomial_diagonal_value hG.
change (((m`!)%:R:C)^-1*:F [tuple x | i<m]=
  ComplexScalars.embed R (((m`!)%:R:R)^-1)*:F [tuple x | i<m]).
by rewrite fmorphV rmorph_nat.
Qed.
End Restriction.
