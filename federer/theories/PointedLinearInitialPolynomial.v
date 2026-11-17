(** Federer (1969), 3.4.11, p. 338:
    an onto linear change of variables preserves the
    original least nonzero Taylor order and carries its
    normalized polynomial by actual composition. Reuse the
    full actual jet transformation from 3.4.8(5). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed AnalyticInitialPolynomialUP
  PointedAnalyticPullbackUP PointedAnalyticLinearPullbackJets PointedAnalyticLinearPullbackDiagonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Transport.
Variable R:realType.
Variables X Y:lmodType R.
Variable NX:X->R.
Variable NY:Y->R.
Variable hNX:is_real_norm NX.
Variable hNY:is_real_norm NY.
Variable L:Hom X Y.
Variable F:analytic_germ_space hNY (0:Y)->analytic_germ_space hNX (0:X).
Hypothesis hF:is_pointed_analytic_germ_pullback L F.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).

(** Source for [pointed_linear_pullback_zero_jet]: a
    zero actual jet remains zero under the linear
    substitutions in 3.4.11, p. 338, by
    the already proved full derivative rule. *)
Lemma pointed_linear_pullback_zero_jet k (alpha:analytic_germ_space hNY (0:Y)):
  @AnalyticGermJets.value R Y NY hNY 0 k alpha=0 ->
  @AnalyticGermJets.value R X NX hNX 0 k (F alpha)=0.
Proof.
move=>hZero;apply:(continuous_multilinear_extensional
  (@ContinuousMultilinear.laws R k X R^o NX N hNX hN))=>u.
rewrite (@pointed_analytic_linear_pullback_jets R X Y NX NY hNX hNY 0 0
  L F hF (linear0 L) k alpha u) hZero !linear0;done.
Qed.

(** Source for [pointed_linear_pullback_nonzero_jet]: onto
    linear substitutions preserve a nonzero actual jet,
    supporting the initial polynomial comparison in 3.4.11,
    p. 338. The onto property supplies only
    preimages of the finite argument tuple. *)
Lemma pointed_linear_pullback_nonzero_jet k (alpha:analytic_germ_space hNY (0:Y)):
  (forall y,exists x,L x=y) ->
  @AnalyticGermJets.value R Y NY hNY 0 k alpha<>0 ->
  @AnalyticGermJets.value R X NX hNX 0 k (F alpha)<>0.
Proof.
move=>hOnto hNonzero hZero;apply:hNonzero.
apply:(continuous_multilinear_extensional
  (@ContinuousMultilinear.laws R k Y R^o NY N hNY hN))=>u.
have [v hV]:=choice (fun i:'I_k=>hOnto (u i)).
have hArgs:[ffun i=>L ([ffun j=>v j] i)]=u.
  by apply/ffunP=>i;rewrite !ffunE hV.
have hEqual:=@pointed_analytic_linear_pullback_jets R X Y NX NY hNX hNY 0 0
  L F hF (linear0 L) k alpha [ffun i=>v i].
rewrite hArgs hZero !linear0 in hEqual.
rewrite linear0;exact:esym hEqual.
Qed.

(** Source for [pointed_linear_initial_polynomial]: the
    exact leading homogeneous polynomial commutes with onto
    linear substitutions, as used in 3.4.11, p. 338.
    Positivity, the first nonzero order, every lower
    zero jet and the original normalization remain. *)
Theorem pointed_linear_initial_polynomial k (alpha:analytic_germ_space hNY (0:Y)) (P:Y->R):
  (forall y,exists x,L x=y) ->is_initial_analytic_germ_polynomial alpha k P ->
  is_initial_analytic_germ_polynomial (F alpha) k (fun x=>P (L x)).
Proof.
move=>hOnto [hPositive [hTop [hLower hFormula]]].
split;first exact:hPositive.
split;first exact:(pointed_linear_pullback_nonzero_jet hOnto hTop).
split;first by move=>i hi;exact:(pointed_linear_pullback_zero_jet (hLower i hi)).
move=>v;rewrite hFormula.
by rewrite (@pointed_analytic_linear_pullback_diagonal R X Y NX NY hNX hNY 0 0
  L F hF (linear0 L) k alpha v).
Qed.
End Transport.
