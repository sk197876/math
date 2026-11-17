(** Federer (1969), 3.4.8(11), p. 333:
    H is the analytic zero set of
    the actual derivative. Finite evaluation on
    a source basis replaces the equivalent
    squared operator-norm equation in the book.
    Analytic derivative evaluations already exist in
    the project; only their connection is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis TensorUP
  NormDifferentialUP NormAnalyticUP NormAnalyticLocal NormClassZeroTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst NormAnalyticFirstJet NormAnalyticDerivativeEvaluation
  FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_critical_variety_exists]:
    the actual critical variety H used
    in the maximum argument, 3.4.8(11),
    p. 333. Prove existence of the
    differential and all analytic scalar equations;
    neither is an added premise. *)
Theorem analytic_critical_variety_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
    (A:set X) (f:X->R^o):
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f ->
  exists (D:X->Hom X R^o) (F:'I_n->X->R^o),
    (forall x,A x ->has_norm_differential NX (fun z:R^o=>`|z|) A f x (D x)) /\
    (forall i,@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX
      (@scalar_absolute_value_norm R) A (F i)) /\
    (forall i x,A x ->F i x = D x (e i)) /\
    @is_finite_analytic_variety R X NX hNX A [set x|A x /\ forall v,D x v = 0].
Proof.
move=>hAnalytic.
pose NR:=fun z:R^o=>`|z|.
pose hNR:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NR hNX hNR.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NR hNX hNR.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX NR hNX hNR.
have hZ i:is_continuous_multilinear_space NX NR (ev i) (NZ i).
  exact:(@ContinuousMultilinear.laws R i X R^o NX NR hNX hNR).
have [J [hJ _]]:=@norm_analytic_first_jet_exists R X R^o NX NR hNX hNR A f hAnalytic.
pose D:=fun x=>@continuous_multilinear_one_operator R X R^o (Z 1%N) NX NR
  (ev 1%N) (NZ 1%N) (hZ 1%N) (J x).
have hD x (hx:A x):has_norm_differential NX NR A f x (D x).
  exact:((@norm_higher_differential_first R X R^o NX NR hNX hNR Z ev NZ hZ A f x (J x)).1
    (hJ x hx)).
have hScalar i:=@norm_analytic_derivative_evaluation_exists R X R^o NX NR hNX hNR
  A f 1%N [ffun _:'I_1=>e i] hAnalytic.
pose F:=fun i:'I_n=>projT1 (cid (hScalar i)).
have hF i:=projT2 (cid (hScalar i)).
have hEquation i x (hx:A x):F i x = D x (e i).
  exact:(hF i).1 x hx (J x) (hJ x hx).
exists D,F;split;first exact:hD.
split;first by move=>i;exact:(hF i).2.
split;first exact:hEquation.
split;first exact:(norm_analytic_domain_open hAnalytic).
exists (Finite.clone 'I_n _),F;split;first by move=>i;exact:(hF i).2.
move=>x;split.
- move=>[hx hZero];split;first exact:hx.
  by move=>i;rewrite hEquation // hZero.
- move=>[hx hZero];split;first exact:hx.
  have hBasis i:D x (e i) = (0:Hom X R^o) (e i).
    by rewrite -hEquation // hZero hom_zeroE.
  move=>v;have h:=@basis_linear_ext R 'I_n X e he R^o
    (hom_as_linear (D x)) (hom_as_linear (0:Hom X R^o)) hBasis v.
  exact:h.
Qed.
