(** Federer (1969), 4.1.1, p. 343: existence of the exact
    finite derivative seminorm. Compact derivative bounds are
    already proved; the generic linear-observation supremum is
    reused without opening its construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm UniformFunctionNormUP LinearObservationSeminormUP LinearObservationSeminormSealed
  SmoothCompactSet SmoothFunctionDerivativesUP SmoothDerivativeCompactBounds SmoothDerivativeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DerivativeSeminormExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable value:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E value D.
Variable K:smooth_compact_set hNX U.
Variable i:nat.
Local Notation J := ({jx:'I_i.+1 * X|smooth_compact_carrier K jx.2}).

(** Source for [smooth_derivative_observation_bound]: compactness
    supplies the boundedness premise of the existing supremum
    theorem, supporting nu^i_K in Federer 4.1.1, p. 343. *)
Lemma smooth_derivative_observation_bound f :
  exists C:R,0<=C /\ forall z:J,
    @ZN (proj1_sig z).1 (@D (proj1_sig z).1 (proj1_sig z).2 f)<=C.
Proof.
have [C [hC hb]]:=smooth_derivative_compact_finite_order_bound hD K f i.
exists C; split=>// z; exact:hb _ _ (proj2_sig z).
Qed.

(** Source for [smooth_derivative_seminorm_exists]: proved
    existence of the exact finite supremum nu^i_K, Federer
    4.1.1, p. 343. Empty K and order zero are included. *)
Theorem smooth_derivative_seminorm_exists :
  exists p,@is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p.
Proof.
pose W(z:J):lmodType R:=Z (proj1_sig z).1.
pose N(z:J):W z->R:=@ZN (proj1_sig z).1.
pose L(z:J):Hom E (W z):=@D (proj1_sig z).1 (proj1_sig z).2.
have hN z:is_real_seminorm (N z).
  exact:(continuous_multilinear_norm_is_norm hNY (hZ (proj1_sig z).1)).1.
pose p:=@LinearObservationSeminorm.value R E J W N L hN smooth_derivative_observation_bound.
have hp:=@LinearObservationSeminorm.laws R E J W N L hN smooth_derivative_observation_bound.
exists p; constructor.
- move=>f; exact:uniform_function_norm_nonnegative (hp f).
- move=>f j hj x hx.
  have hj':(j<i.+1)%N by rewrite ltnS.
  pose z:J:=exist _ ((Ordinal hj'),x) hx.
  have hb:=uniform_function_norm_bound (hp f) z.
  change (is_true (`|@ZN j (@D j x f)|<=p f)) in hb.
  by rewrite (ger0_norm (real_seminorm_nonnegative
    (continuous_multilinear_norm_is_norm hNY (hZ j)).1 (@D j x f))) in hb.
- move=>f C hC hb.
  apply:(@uniform_function_norm_least R J _ _ (hp f) C hC)=>z.
  rewrite (ger0_norm (real_seminorm_nonnegative (hN z) (L z f))).
  have hj:((proj1_sig z).1<=i)%N by move:(ltn_ord (proj1_sig z).1); rewrite ltnS.
  exact:hb _ hj _ (proj2_sig z).
Qed.
End DerivativeSeminormExistence.
