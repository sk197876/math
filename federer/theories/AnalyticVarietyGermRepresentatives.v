(** Federer (1969), 3.4.5, p. 320: every
    analytic variety germ has an actual finite equation
    system of analytic-germ representatives on one neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP
  SetGermUP FiniteAnalyticVarietyUP FiniteZeroSetSealed AnalyticVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_variety_germ_equation_system]: the
    original definition of V_a(X), expressed through actual
    analytic representatives, 3.4.5, p. 320. *)
Theorem analytic_variety_germ_equation_system (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_analytic_variety_germ R X NX hNX a alpha ->
  exists J:finType,exists f:J->@analytic_representative_type R X NX hNX a,
  exists U:set X,U a /\@open (real_norm_metric_space hNX) U /\
    (forall j,@norm_analytic R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
      U (analytic_representative_value (f j))) /\
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a
      (@FiniteZeroSet.value [the zmodType of R^o] X U J (fun j=>analytic_representative_value (f j)))=alpha.
Proof.
move=>[U [S [ha [[hU [J [g [hg hS]]]] hGerm]]]].
have hex j:=@analytic_representative_from_domain R X NX hNX a U (g j) (hg j a ha).
pose f j:=projT1 (cid (hex j)).
have hf j:=projT2 (cid (hex j)).
have hFunction:(fun j=>analytic_representative_value (f j))=g by apply:funext=>j;exact:hf.
exists J,f,U;split;first exact:ha.
split;first exact:hU.
split.
- by move=>j;rewrite hf;exact:hg j.
- have hSet:(@FiniteZeroSet.value [the zmodType of R^o] X U J g)=S.
    apply/seteqP;split=>x;by rewrite (original_zero_set_membership (FiniteZeroSet.laws U g) x) (hS x).
  by rewrite hFunction hSet.
Qed.
