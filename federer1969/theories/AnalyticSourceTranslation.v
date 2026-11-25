(** Federer (1969), 3.4.8(11), p. 333:
    the induction applies at each centre of
    the critical variety. Actual source translations
    retain analyticity and the finite defining equations;
    their inverses supply the local component transport. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormClosureLaws
  NormAnalyticUP NormAnalyticTranslation NormAnalyticComposition NormAnalyticOperations
  FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_source_translation]:
    translate an original analytic function to
    zero when applying the induction at a,
    3.4.8(11), p. 333. *)
Theorem norm_analytic_source_translation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) (a:X):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R X Y NX NY hNX hNY [set x|A (a+x)] (fun x=>f (a+x)).
Proof.
move=>hAnalytic.
have [hTranslation _]:=@norm_translations_analytic R X NX hNX setT
  (fun x _=>norm_full_domain_interior NX x) a.
have hComposite:=@norm_analytic_composition R X X Y NX NX NY hNX hNX hNY
  setT A (fun x=>x+a) f hTranslation hAnalytic.
have hDomain:[set x:X|setT x /\ A (x+a)] = [set x:X|A (a+x)].
  apply/seteqP;split=>x hx.
  - change (A (a+x));rewrite addrC;exact:hx.2.
  - change (True /\ A (x+a));split;first exact:Logic.I.
    by rewrite addrC.
change (@norm_analytic R X Y NX NY hNX hNY
  [set x:X|setT x /\ A (x+a)] (fun x=>f (x+a))) in hComposite.
rewrite hDomain in hComposite.
apply:(@norm_analytic_domain_agreement R X Y NX NY hNX hNY
  [set x|A (a+x)] (fun x=>f (x+a)) (fun x=>f (a+x)) _ hComposite).
by move=>x _;rewrite addrC.
Qed.

(** Source for [finite_analytic_variety_source_translation]:
    the actual critical equations remain analytic
    at every translated centre used in
    3.4.8(11), p. 333. *)
Theorem finite_analytic_variety_source_translation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A S:set X) a:
  @is_finite_analytic_variety R X NX hNX A S ->
  @is_finite_analytic_variety R X NX hNX [set x|A (a+x)] [set x|S (a+x)].
Proof.
move=>[hOpen [I [F [hF hEquation]]]].
split.
- exact:(@open_comp (real_norm_metric_space hNX) (real_norm_metric_space hNX)
    (fun x=>a+x) A (fun x _=>@real_norm_metric_translate_continuous R X NX hNX a x) hOpen).
- exists I,(fun i x=>F i (a+x));split.
  + move=>i;exact:norm_analytic_source_translation (hF i).
  + move=>x;exact:hEquation (a+x).
Qed.
