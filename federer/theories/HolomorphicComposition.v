(** Federer (1969), 3.4.12, p. 338:
    composition preserves the original holomorphic condition.
    Apply real analytic composition, the actual chain rule
    and differential uniqueness; retain the exact composite domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP NormDifferentialChain NormDifferentialDirectional
  NormAnalyticComposition HolomorphicUP HolomorphicDifferentialUP
  HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_composition]: the composition
    laws of 3.1.24, pp. 239–240, with the
    original complex differential condition of 3.4.12,
    p. 338. No global inclusion of the first
    image in the second domain is required. *)
Theorem holomorphic_composition (R:realType)
    (X Y Z:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    (hNY:is_real_norm (fun y:restricted_space (ComplexScalars.embed R) Y=>NY y))
    (hNZ:is_real_norm (fun z:restricted_space (ComplexScalars.embed R) Z=>NZ z))
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->Z):
  is_holomorphic hNX hNY A f ->is_holomorphic hNY hNZ B g ->
  is_holomorphic hNX hNZ (fun x=>A x /\B (f x)) (fun x=>g (f x)).
Proof.
move=>hF hG;split;first exact:norm_analytic_composition hF.1 hG.1.
move=>a L [ha hb] hActual.
have [D [LD [hLD hD]]]:=holomorphic_differential_exists hF ha.
have [E [LE [hLE hE]]]:=holomorphic_differential_exists hG hb.
have hChain:=norm_differential_chain hNX hNY hNZ hLD hLE.
have hEqual:=norm_differential_unique hNX hNZ hActual hChain.
have hLDc:=hF.2 a LD ha hLD.
have hLEc:=hG.2 (f a) LE hb hLE.
move=>c x;rewrite hEqual !hom_compE.
change (LE (LD (c*:(x:X)))=c*:(LE (LD x):Z)).
by rewrite hLDc hLEc.
Qed.
