(** Federer (1969), 3.4.5, p. 319: composition with
    an actual map analytic at the original centre gives an
    actual analytic representative at that centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormClassZeroTopology
  NormAnalyticUP NormAnalyticComposition NormAnalyticDomain NormAnalyticLocal
  AnalyticGermNeighbourhood AnalyticGermRepresentatives LocalGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Composition.
Variable R:realType.
Variables X Y:lmodType R.
Variable NX:X->R.
Variable NY:Y->R.
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable A:set X.
Variable u:X->Y.
Variable a:X.
Hypothesis hu:@norm_analytic_at R X Y NX NY hNX hNY A u a.

(** Source for [analytic_pullback_representative_analytic]:
    the composite in the displayed homomorphism equation of
    3.4.5, p. 319, is analytic at a. *)
Lemma analytic_pullback_representative_analytic
    (f:@analytic_representative_type R Y NY hNY (u a)):
  @norm_analytic_at R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
    setT (fun x=>analytic_representative_value f (u x)) a.
Proof.
have hComp:=@norm_analytic_at_composition R X Y R^o NX NY (fun z=>`|z|)
  hNX hNY (@scalar_absolute_value_norm R) A setT u (analytic_representative_value f) a
  hu (analytic_representative_analytic f).
exact:(@norm_analytic_at_domain_enlargement R X R^o NX (fun z=>`|z|)
  hNX (@scalar_absolute_value_norm R) (fun x=>A x /\ setT (u x)) setT _ a
  (fun x hx=>Logic.I) hComp).
Qed.

(** Source for [analytic_pullback_representative]: the actual
    representative h composed with u, 3.4.5, p. 319. *)
Definition analytic_pullback_representative
    (f:@analytic_representative_type R Y NY hNY (u a)):
    @analytic_representative_type R X NX hNX a:=
  exist _ (fun x=>analytic_representative_value f (u x))
    (analytic_pullback_representative_analytic f).

(** Source for [analytic_pullback_preserves_local_equality]:
    the displayed map in 3.4.5, p. 319, depends
    only on the original germ of h. Continuity of the actual
    analytic map pulls a target neighbourhood back to a source
    neighbourhood; no global regularity outside it is required. *)
Lemma analytic_pullback_preserves_local_equality
    (f g:@analytic_representative_type R Y NY hNY (u a)):
  @locally_equal_at (Topological.clone (real_norm_metric_space hNY) _) R (u a)
    (analytic_representative_value f) (analytic_representative_value g) ->
  @locally_equal_at (Topological.clone (real_norm_metric_space hNX) _) R a
    (analytic_representative_value (analytic_pullback_representative f))
    (analytic_representative_value (analytic_pullback_representative g)).
Proof.
move=>[V [hV [hVa hEq]]].
have [U [hUa [hUA [hU hAnalytic]]]]:=analytic_germ_open_representative hu.
have hClass:=norm_class_continuous (norm_analytic_class_all_orders hAnalytic 0%N).
have hNear:=@norm_class_zero_continuous_at R X Y NX NY hNX hNY U u a hClass hUa V
  (open_nbhs_nbhs (conj hV hVa)).
change (nbhs (a:real_norm_metric_space hNX) (fun x=>V (u x))) in hNear.
rewrite nbhsE in hNear.
have [W [hW hWa] hWV]:=hNear.
exists W;split;first exact:hW.
split;first exact:hWa.
move=>x hx;exact:hEq (u x) (hWV x hx).
Qed.
End Composition.
