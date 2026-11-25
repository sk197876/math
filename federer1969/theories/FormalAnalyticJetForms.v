(** Federer (1969), 3.4.5, p. 319: symmetric
    coefficient sequences have actual bounded Chapter 1 form
    representatives with exactly the same operator norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms SymmetricOperatorNorm MultilinearTupleForm ContinuousMultilinearSymmetricNorm
  ContinuousSymmetricFormAdapter FormalAnalyticJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [formal_analytic_jet_forms_exists]: the
    symmetric coefficient forms in the compactness argument
    of 3.4.5, p. 319. Algebraic symmetry, bounded
    multilinear evaluation and the exact operator norm suffice;
    analytic realisation is not assumed. *)
Theorem formal_analytic_jet_forms_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) s t
    (w:forall m,@ContinuousMultilinear.space R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)):
  is_formal_analytic_jet s t w ->exists phi:forall m,S_m X R^o m,
    (forall m u,phi m u=@ContinuousMultilinear.evaluation R m X R^o NX (fun z=>`|z|)
      hNX (@scalar_absolute_value_norm R) [ffun i=>tnth u i] (w m)) /\
    (forall m,norm_bounded_symmetric_form NX (fun z:R^o=>`|z|) (phi m)) /\
    forall m,symmetric_operator_norm hNX.1 (fun z:R^o=>`|z|) (phi m)=
      (@ContinuousMultilinear.norm R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R) (w m))%:E.
Proof.
move=>hw.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z m:=@ContinuousMultilinear.space R m X R^o NX NS hNX hNS.
pose ev m:=@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS.
pose ZN m:=@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS.
have hZ m:is_continuous_multilinear_space NX NS (ev m) (ZN m).
  exact:ContinuousMultilinear.laws.
have hex m:exists phi:S_m X R^o m,forall u,phi u=ev m [ffun i=>tnth u i] (w m).
  exact:(@symmetric_multilinear_tuple_form_exists R X R^o m (fun u=>ev m u (w m))
    (continuous_multilinear_evaluation (hZ m) (w m))
    (@formal_analytic_jet_symmetric R X NX hNX s t w hw m)).
pose phi m:=projT1 (cid (hex m)).
have hPhi m:=projT2 (cid (hex m)).
have hNorm m:symmetric_operator_norm hNX.1 NS (phi m)=(ZN m (w m))%:E.
  exact:(@continuous_multilinear_symmetric_norm R m X R^o (Z m) NX NS hNX hNS
    (ev m) (ZN m) (hZ m) (w m) (phi m) (hPhi m)).
exists phi;split;first exact:hPhi.
split;last exact:hNorm.
move=>m;apply:(@finite_operator_norm_sform_bounded R m X R^o NX NS hNX hNS (phi m)
  (s%:R*t%:R^+m*(m`!)%:R)).
rewrite hNorm lee_fin;exact:(@formal_analytic_jet_growth R X NX hNX s t w hw m).
Qed.
