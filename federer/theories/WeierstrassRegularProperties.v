(** Federer (1969), 3.4.6, pp. 321–322: the printed
    directional regularity forces a nonzero direction and a
    nonzero analytic germ. These consequences discharge the
    normalizations and retain the degenerate source boundary. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermJetZeroNegate WeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Regularity.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation jet:=(@AnalyticGermJets.value R X NX hNX 0).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX N hNX hN).

(** Source for [weierstrass_regular_germ_nonzero]: the actual
    nonzero kth directional derivative excludes the zero germ,
    supporting the normalization in 3.4.6, pp. 321–322. *)
Lemma weierstrass_regular_germ_nonzero (alpha:analytic_germ_space hNX (0:X)) k v:
  @is_weierstrass_regular_germ R X NX hNX alpha k v ->
  alpha<>@analytic_germ_zero R X NX hNX 0.
Proof.
move=>[_ [_ hTop]] hZero;apply:hTop.
by rewrite hZero analytic_germ_jet_zero linear0.
Qed.

(** Source for [weierstrass_regular_direction_nonzero]: the
    positive kth derivative order forces the actual original
    v to be nonzero, supporting the choice of xi in
    3.4.6, p. 322. No dimension premise is added. *)
Lemma weierstrass_regular_direction_nonzero (alpha:analytic_germ_space hNX (0:X)) k v:
  @is_weierstrass_regular_germ R X NX hNX alpha k v ->v<>0.
Proof.
move=>[hK [_ hTop]] hv;subst v;apply:hTop.
have hBound:=multilinear_operator_bound (continuous_multilinear_norm_laws (hZ k) (jet k alpha))
  [ffun _:'I_k=>(0:X)].
have hProduct:(\prod_(i<k) NX ([ffun _:'I_k=>(0:X)] i))=0.
  under eq_bigr do rewrite ffunE (real_seminorm_zero hNX.1).
  have hNonzero:k!=0%N by rewrite -lt0n.
  by rewrite prodr_const card_ord expr0n (negbTE hNonzero).
rewrite hProduct mulr0 in hBound.
apply/eqP;rewrite -normr_eq0;apply/eqP.
apply/eqP;rewrite eq_le;apply/andP;split;[exact:hBound|exact:normr_ge0].
Qed.
End Regularity.
