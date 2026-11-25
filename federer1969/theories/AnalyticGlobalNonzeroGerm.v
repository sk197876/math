(** Federer (1969), 3.4.10, p. 338:
    the cited polynomial equation has a nonzero
    germ at every centre. This supporting
    connection applies the existing analytic identity
    theorem on the connected whole normed space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormSpaceConnected NormAnalyticUP
  AnalyticIdentityOpenZero LocalGermUP LocalGermSealed AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_global_nonzero_germ]: a
    globally analytic function with one nonzero value
    cannot have the zero germ at any
    centre. This supplies an actual nonzero
    ideal member for the example in 3.4.10,
    p. 338; it reuses 3.1.24's
    proved identity theorem, pp. 239-240. *)
Theorem analytic_global_nonzero_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (p:@analytic_representative_type R X NX hNX a):
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    setT (analytic_representative_value p) ->
  (exists b,analytic_representative_value p b<>0) ->
  @analytic_germ R X NX hNX a p<>@analytic_germ_zero R X NX hNX a.
Proof.
move=>hAnalytic [b hb] hZero.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
change (analytic_germ p=analytic_germ (@analytic_constant_representative R X NX hNX a 0)) in hZero.
move/(local_germ_equality (@LocalGerms.laws T R P value a)):hZero=>
  [U [hU [haU hEqual]]].
have hVanishing x (hx:U x):analytic_representative_value p x=0:=hEqual x hx.
have hGlobal:=@analytic_identity_open_zero R X R^o NX (fun t=>`|t|) hNX
  (@scalar_absolute_value_norm R) setT U (analytic_representative_value p) a
  (@real_norm_space_connected R X NX hNX) hAnalytic hU haU
  (fun _ _=>Logic.I) hVanishing.
exact:hb (hGlobal b Logic.I).
Qed.
