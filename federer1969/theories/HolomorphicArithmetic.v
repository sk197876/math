(** Federer (1969), 3.4.12, p. 339:
    the original holomorphic function classes are closed
    under addition and contain every constant. Apply real
    analytic arithmetic and actual differential uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed RealNormUP
  NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormDifferentialDirectional
  NormAnalyticConstant NormAnalyticOperations HolomorphicUP HolomorphicDifferentialUP
  HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variable NX:XR->R.
Variable NY:YR->R.
Variable hNX:is_real_norm NX.
Variable hNY:is_real_norm NY.
Variable A:X->Prop.
Local Notation HOL f:=(@is_holomorphic R X Y NX NY hNX hNY A f).

(** Source for [holomorphic_add]: original holomorphic
    functions form an additive class in the complex
    version of 3.4.5, p. 319, specified
    in 3.4.12, p. 339. *)
Theorem holomorphic_add (f g:X->Y):HOL f ->HOL g ->HOL (fun x=>f x+g x).
Proof.
move=>hF hG;split;first exact:norm_analytic_add hF.1 hG.1.
move=>a L ha hActual.
have [D [LD [hLD hD]]]:=holomorphic_differential_exists hF ha.
have [E [LE [hLE hE]]]:=holomorphic_differential_exists hG ha.
have hSum:=norm_differential_add hNY hLD hLE.
have hEqual:=norm_differential_unique hNX hNY hActual hSum.
have hLDc:=hF.2 a LD ha hLD.
have hLEc:=hG.2 a LE ha hLE.
move=>c x;rewrite hEqual !hom_addE.
change (LD (c*:(x:X))+LE (c*:(x:X))=c*:(LD x+LE x:Y)).
by rewrite hLDc hLEc scalerDr.
Qed.

(** Source for [holomorphic_constant]: every constant
    is an original holomorphic function, including the
    zero and unit functions of the complex local
    ring in 3.4.12, p. 339. *)
Theorem holomorphic_constant (c:Y):
  (forall a,A a ->norm_domain_interior NX A a) ->HOL (fun _=>c).
Proof.
move=>hA;split;first exact:(@norm_constant_analytic R XR YR NX NY hNX hNY A hA c).
move=>a L ha hActual.
have hZero:=@norm_differential_constant R XR YR NX NY hNX hNY A a c (hA a ha).
have hEqual:=norm_differential_unique hNX hNY hActual hZero.
move=>z x;by rewrite hEqual !hom_zeroE scaler0.
Qed.
End Arithmetic.
