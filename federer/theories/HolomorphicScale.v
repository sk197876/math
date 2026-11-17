(** Federer (1969), 3.4.12, p. 339: multiplication by an
    arbitrary complex scalar preserves holomorphy. Reuse bounded real
    postcomposition and the actual first derivative; scalar commutation
    supplies its complex linearity, including scalar zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexScalarRealBounded NormAnalyticUP NormAnalyticOperations NormAnalyticBoundedPostcompose
  NormDifferentialUP NormDifferentialFiniteCalculus NormDifferentialLocal NormDifferentialDirectional
  HolomorphicUP HolomorphicDifferentialUP HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Scale.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variables (NX:XR->R) (NY:Y->R).
Variable hNX:is_real_norm NX.
Variable hNY:is_complex_norm NY.
Local Notation hNYR:=(complex_norm_real hNY).

(** Source for [holomorphic_scale]: the complex scalar closure
    of the original holomorphic functions and their germs in
    3.4.12, p. 339, supporting the original normalization in
    3.4.6, p. 322. No scalar is assumed invertible here. *)
Theorem holomorphic_scale (A:X->Prop) (f:X->Y) (c:ComplexScalars.C R):
  is_holomorphic hNX hNYR A f ->is_holomorphic hNX hNYR A (fun x=>c*:f x).
Proof.
move=>hF.
have [M [hValues hM]]:=@complex_scalar_real_bounded_exists R Y NY hNY c.
have hAnalytic:=@norm_analytic_bounded_postcompose R XR YR YR NX NY NY hNX hNYR hNYR
  A f M hF.1 hM.
split.
- apply:(@norm_analytic_domain_agreement R XR YR NX NY hNX hNYR A
    (fun x=>M (f x)) (fun x=>c*:f x) _ hAnalytic)=>x _;exact:hValues.
- move=>a L ha hL.
  have [D [LD [hLD hD]]]:=holomorphic_differential_exists hF ha.
  have hPost:=@norm_differential_postcompose R XR YR YR NX NY NY hNX A f a LD M hLD hM.
  have hOriginal:=@norm_differential_domain_agreement R XR YR NX NY hNX A
    (fun x=>M (f x)) (fun x=>c*:f x) a (hom_comp M LD) (fun x _=>hValues (f x)) hPost.
  have hEqual:=norm_differential_unique hNX hNYR hL hOriginal.
  have hComplex:=hF.2 a LD ha hLD.
  move=>z v;rewrite hEqual !hom_compE !hValues hComplex.
  change (c*:(z*:(LD v:Y))=z*:(c*:(LD v:Y))).
  by rewrite !scalerA mulrC.
Qed.
End Scale.
