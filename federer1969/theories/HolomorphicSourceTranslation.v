(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(11), p. 333:
    the induction applies at each centre of
    the critical variety. Actual source translations
    retain analyticity and the finite defining equations;
    their inverses supply the local component transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicTranslations HolomorphicComposition HolomorphicRestriction RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormClosureLaws
  NormAnalyticUP NormAnalyticTranslation NormAnalyticComposition NormAnalyticOperations
  FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_source_translation]:
    translate an original analytic function to
    zero when applying the induction at a,
    3.4.8(11), p. 333. *)
Theorem holomorphic_source_translation (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (f:X->Y) (a:X):
  @is_holomorphic R X Y NX NY hNX hNY A f ->
  @is_holomorphic R X Y NX NY hNX hNY [set x|A (a+x)] (fun x=>f (a+x)).
Proof.
move=>hAnalytic.
have [hTranslation _]:=@holomorphic_translations R X NX hNX setT
  (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x) a.
have hComposite:=@holomorphic_composition R X X Y NX NX NY hNX hNX hNY
  setT A (fun x=>x+a) f hTranslation hAnalytic.
have hDomain:[set x:X|setT x /\ A (x+a)] = [set x:X|A (a+x)].
  apply/seteqP;split=>x hx.
  - change (A (a+x));rewrite addrC;exact:hx.2.
  - change (True /\ A (x+a));split;first exact:Logic.I.
    by rewrite addrC.
change (@is_holomorphic R X Y NX NY hNX hNY
  [set x:X|setT x /\ A (x+a)] (fun x=>f (x+a))) in hComposite.
rewrite hDomain in hComposite.
apply:(@holomorphic_domain_agreement R X Y NX NY hNX hNY
  [set x|A (a+x)] (fun x=>f (x+a)) (fun x=>f (a+x)) _ hComposite).
by move=>x _;rewrite addrC.
Qed.

(** Source for [finite_holomorphic_variety_source_translation]:
    the actual critical equations remain analytic
    at every translated centre used in
    3.4.8(11), p. 333. *)
Theorem finite_holomorphic_variety_source_translation (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (A S:set X) a:
  @is_finite_holomorphic_variety R X NX hNX A S ->
  @is_finite_holomorphic_variety R X NX hNX [set x|A (a+x)] [set x|S (a+x)].
Proof.
move=>[hOpen [I [F [hF hEquation]]]].
split.
- exact:(@open_comp (real_norm_metric_space hNX) (real_norm_metric_space hNX)
    (fun x=>a+x) A (fun x _=>@real_norm_metric_translate_continuous R (restricted_space (ComplexScalars.embed R) X) NX hNX a x) hOpen).
- exists I,(fun i x=>F i (a+x));split.
  + move=>i;exact:holomorphic_source_translation (hF i).
  + move=>x;exact:hEquation (a+x).
Qed.
