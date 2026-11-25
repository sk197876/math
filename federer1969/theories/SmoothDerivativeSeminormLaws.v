(** Federer (1969), 4.1.1, pp. 343–344: consequences of the
    independent least-bound definition of nu^i_K. No supremum
    witness or smooth-function implementation is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm UniformFunctionNormUP LinearObservationSeminormUP
  LinearObservationSeminormLaws SmoothCompactSet SmoothDerivativeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DerivativeSeminormLaws.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Variable K:smooth_compact_set hNX U.
Variable i:nat.
Variable p:E->R.
Hypothesis hp:@is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i p.
Local Notation J := ({jx:'I_i.+1 * X|smooth_compact_carrier K jx.2}).

(** Source for [smooth_derivative_seminorm_observations]: the
    exact derivative bound is the uniform norm of its actual
    linear observations, supporting Federer 4.1.1, p. 343. *)
Lemma smooth_derivative_seminorm_observations :
  is_linear_observation_seminorm
    (fun z:J=>@ZN (proj1_sig z).1)
    (fun z:J=>@D (proj1_sig z).1 (proj1_sig z).2) p.
Proof.
move=>f; constructor.
- exact:(smooth_derivative_seminorm_nonnegative hp f).
- move=>z.
  rewrite (ger0_norm (real_seminorm_nonnegative
    (continuous_multilinear_norm_is_norm hNY (hZ (proj1_sig z).1)).1 _)).
  have hj:((proj1_sig z).1<=i)%N by move:(ltn_ord (proj1_sig z).1); rewrite ltnS.
  exact:(smooth_derivative_seminorm_bound hp f hj (proj2_sig z)).
- move=>C hC hb; apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K i p hp f C hC)=>j hj x hx.
  have hj':(j<i.+1)%N by rewrite ltnS.
  pose z:J:=exist _ ((Ordinal hj'),x) hx.
  have h:=hb z.
  change (is_true (`|@ZN j (@D j x f)|<=C)) in h.
  by rewrite (ger0_norm (real_seminorm_nonnegative
    (continuous_multilinear_norm_is_norm hNY (hZ j)).1 _)) in h.
Qed.

(** Source for [smooth_derivative_seminorm_is_seminorm]: nu^i_K
    is a seminorm, Federer 4.1.1, pp. 343–344. The proof includes
    K empty and i=0 and uses only the exact-bound laws. *)
Theorem smooth_derivative_seminorm_is_seminorm : is_real_seminorm p.
Proof.
apply:(linear_observation_seminorm_is_seminorm _ smooth_derivative_seminorm_observations)=>z.
exact:(continuous_multilinear_norm_is_norm hNY (hZ (proj1_sig z).1)).1.
Qed.

(** Source for [smooth_derivative_seminorm_monotone]: increasing
    the compact set and derivative order increases the seminorm,
    supporting the basic neighbourhoods in Federer 4.1.1, p. 344. *)
Theorem smooth_derivative_seminorm_monotone
    (L:smooth_compact_set hNX U) j q :
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D L j q ->
  (i<=j)%N -> smooth_compact_carrier K `<=` smooth_compact_carrier L ->
  forall f,p f<=q f.
Proof.
move=>hq hij hKL f.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K i p hp f (q f)
  (smooth_derivative_seminorm_nonnegative hq f))=>k hk x hx.
exact:(smooth_derivative_seminorm_bound hq f (leq_trans hk hij) (hKL x hx)).
Qed.

(** Source for [smooth_derivative_seminorm_unique]: supporting
    uniqueness of the printed nu^i_K, Federer 4.1.1, p. 343. *)
Theorem smooth_derivative_seminorm_unique q :
  @is_smooth_derivative_seminorm R X Y NX NY hNX hNY U E D K i q -> p = q.
Proof.
move=>hq; apply:funext=>f; apply/eqP; rewrite eq_le; apply/andP; split.
- exact:(smooth_derivative_seminorm_monotone hq (leqnn i) (fun x hx=>hx) f).
- apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY U E D K i q hq f (p f)
    (smooth_derivative_seminorm_nonnegative hp f))=>j hj x hx.
  exact:(smooth_derivative_seminorm_bound hp f hj hx).
Qed.
End DerivativeSeminormLaws.
