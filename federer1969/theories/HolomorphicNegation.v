(** Federer (1969), 3.4.12, p. 339:
    the original holomorphic functions are closed under
    additive negation. Reuse real analytic negation, the
    actual real scalar derivative rule and uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP NormDifferentialArithmetic NormDifferentialDirectional
  NormAnalyticArithmeticLocal HolomorphicUP HolomorphicDifferentialUP HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Negation.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variables (NX:XR->R) (NY:YR->R).
Variable hNX:is_real_norm NX.
Variable hNY:is_real_norm NY.
Variable A:X->Prop.

(** Source for [holomorphic_negate]: additive inverses
    remain original holomorphic functions in the complex
    local ring of 3.4.12, p. 339. *)
Theorem holomorphic_negate (f:X->Y):
  is_holomorphic hNX hNY A f ->is_holomorphic hNX hNY A (fun x=> -f x).
Proof.
move=>hF;split.
- move=>a ha;exact:(@norm_analytic_at_negate R XR YR NX NY hNX hNY A f a (hF.1 a ha)).
- move=>a L ha hActual.
  have [D [M [hM hD]]]:=holomorphic_differential_exists hF ha.
  have hNeg:=@norm_differential_scale R XR YR NX NY hNX hNY A f a M (-1) hM.
  have hFunction:(fun x:X=>(-1:R)*:(f x:YR))=(fun x:X=> -f x).
    by apply:funext=>x;rewrite scaleN1r.
  rewrite hFunction in hNeg.
  have hEqual:=norm_differential_unique hNX hNY hActual hNeg.
  have hComplex:=hF.2 a M ha hM.
  move=>c x;rewrite hEqual !hom_scaleE !scaleN1r.
  change (-M (c*:(x:X))=c*:(-M x:Y)).
  by rewrite hComplex scalerN.
Qed.
End Negation.
