(** Federer (1969), 3.4.5, p. 319: the
    permutation equations of actual derivative coefficients are closed.
    This supports compactness of the bounded derivative sequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  ContinuousMultilinearEvaluationBound FiniteArgumentPermutation ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ClosedSymmetry.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable P:topologicalType.
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m X R^o NX NS hNX hNS).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS).
Local Notation hZN:=(fun m=>continuous_multilinear_norm_is_norm hNS (hZ m)).
Variable J:forall m,P->Z m.
Arguments J m _ : clear implicits.
Hypothesis hJ:forall m,continuous (fun p:P=>(J m p:real_norm_metric_space (hZN m))).

(** Source for [jet_symmetry_locus_closed]: the derivative
    symmetry constraints needed for the compactness assertion
    of 3.4.5, p. 319, are closed. Each fixed-tuple
    evaluation is bounded linear, and the scalar target is
    Hausdorff. Intersect their actual equality loci in every order. *)
Theorem jet_symmetry_locus_closed:
  closed [set p:P|forall m (sigma:'S_m) (u:{ffun 'I_m->X}),
    ev m (finite_argument_permutation sigma u) (J m p)=ev m u (J m p)].
Proof.
have hEquation:[set p:P|forall m (sigma:'S_m) (u:{ffun 'I_m->X}),
    ev m (finite_argument_permutation sigma u) (J m p)=ev m u (J m p)]=
    \bigcap_(m in @setT nat) \bigcap_(sigma in @setT 'S_m)
      \bigcap_(u in @setT {ffun 'I_m->X})
        [set p:P|ev m (finite_argument_permutation sigma u) (J m p)=ev m u (J m p)].
  apply/seteqP;split=>p hp.
  - move=>m _ sigma _ u _;exact:hp m sigma u.
  - move=>m sigma u;exact:hp m Logic.I sigma Logic.I u Logic.I.
rewrite hEquation;apply:closed_bigI=>m _;apply:closed_bigI=>sigma _;apply:closed_bigI=>u _.
pose S:=real_norm_metric_space hNS.
have hEvaluation (v:{ffun 'I_m->X}):continuous (fun p:P=>(ev m v (J m p):S)).
  have hEval:continuous (fun z:real_norm_metric_space (hZN m)=>(ev m v z:S)).
    exact:(@norm_bounded_linear_continuous R (Z m) R^o (ZN m) NS (hZN m) hNS (ev m v)
      (@continuous_multilinear_evaluation_bounded R m X R^o (Z m) NX NS hNX (ev m) (ZN m) (hZ m) v)).
  move=>p.
  exact:(@continuous_comp P (Topological.clone (real_norm_metric_space (hZN m)) _)
    (Topological.clone S _) (fun p:P=>(J m p:real_norm_metric_space (hZN m)))
    (fun z:real_norm_metric_space (hZN m)=>(ev m v z:S)) p (@hJ m p) (hEval (J m p))).
exact:(@continuous_equalizer_closed P (Topological.clone S _)
  (fun p=>(ev m (finite_argument_permutation sigma u) (J m p):S))
  (fun p=>(ev m u (J m p):S)) (@metric_hausdorff R S)
  (hEvaluation (finite_argument_permutation sigma u)) (hEvaluation u)).
Qed.
End ClosedSymmetry.
