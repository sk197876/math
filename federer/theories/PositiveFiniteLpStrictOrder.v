(** Federer (1969), 2.5.7, p. 99: the function tau(u)=phi_(q)(u) is strictly
    increasing on nonnegative densities modulo almost equality when q is
    finite. These supporting proofs integrate the positive qth powers and
    use equality in integral order; they do not assume a strictness law for
    an arbitrary seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralComparison MeasureIntegralOrderEquality
  RealPower ExtendedPositivePower TotalScalarLpUP TotalScalarLpNormLaws TotalScalarLpFiniteSeminorm
  FiniteLpLowerLimitFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_finite_lp_norm_almost_order]: weak monotonicity of
    tau in Federer 2.5.7, p. 99 The comparison is allowed to fail on a null
    set, as in Federer's order on U. *)
Lemma positive_finite_lp_norm_almost_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : R) (u v : X -> R) :
  total_scalar_lp mu q%:E u -> total_scalar_lp mu q%:E v ->
  (forall x, (0 <= u x)%R) -> (forall x, (0 <= v x)%R) ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  (finite_total_scalar_lp_norm mu q%:E u <= finite_total_scalar_lp_norm mu q%:E v)%R.
Proof.
move=> hu hv hu0 hv0 huv.
have hq : (0 < q)%R.
  have h1 : (1 <= q)%R by move: hu.1; rewrite lee_fin.
  exact: lt_le_trans ltr01 h1.
have hui := @nonnegative_total_lp_power_integral R X mu hm q u hu hu0.
have hvi := @nonnegative_total_lp_power_integral R X mu hm q v hv hv0.
have hi : (real_power (finite_total_scalar_lp_norm mu q%:E u) q)%:E <=
    (real_power (finite_total_scalar_lp_norm mu q%:E v) q)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hui hvi).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huv)=> x hx.
  exists (real_power (u x) q)%:E,(real_power (v x) q)%:E; split=> //; split=> //.
  change (is_true (real_power (u x) q <= real_power (v x) q)%R).
  exact: real_power_monotone (hu0 x) hx hq.
have hnu : (0 <= finite_total_scalar_lp_norm mu q%:E u)%R.
  apply: fine_ge0; exact: (@total_scalar_lp_norm_nonnegative R X mu hm _ _ hu.1 hu.2.1).
have hnv : (0 <= finite_total_scalar_lp_norm mu q%:E v)%R.
  apply: fine_ge0; exact: (@total_scalar_lp_norm_nonnegative R X mu hm _ _ hv.1 hv.2.1).
by rewrite lee_fin (real_power_order_embedding hnu hnv hq) in hi.
Qed.

(** Source for [positive_finite_lp_equal_norm_almost_equal]: the equality
    case proving strictness of tau in Federer 2.5.7, p. 99 Ordered
    nonnegative functions of equal finite Lq norm agree almost everywhere;
    infinity is excluded from q. *)
Lemma positive_finite_lp_equal_norm_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : R) (u v : X -> R) :
  total_scalar_lp mu q%:E u -> total_scalar_lp mu q%:E v ->
  (forall x, (0 <= u x)%R) -> (forall x, (0 <= v x)%R) ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  finite_total_scalar_lp_norm mu q%:E u=finite_total_scalar_lp_norm mu q%:E v ->
  measure_almost_everywhere mu [set x | u x=v x].
Proof.
move=> hu hv hu0 hv0 huv he.
have hq : (0 < q)%R.
  have h1 : (1 <= q)%R by move: hu.1; rewrite lee_fin.
  exact: lt_le_trans ltr01 h1.
have hui := @nonnegative_total_lp_power_integral R X mu hm q u hu hu0.
have hvi := @nonnegative_total_lp_power_integral R X mu hm q v hv hv0.
rewrite -he in hvi.
have heq := @measure_integral_order_equality R X mu hm _ _ _ hui hvi.
have horder : measure_almost_everywhere mu [set x | exists a b : R,
    partial_function_graph (partial_function_total (fun x => extended_positive_power (u x)%:E q)) x a%:E /\
    partial_function_graph (partial_function_total (fun x => extended_positive_power (v x)%:E q)) x b%:E /\ (a <= b)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huv)=> x hx.
  exists (real_power (u x) q),(real_power (v x) q); split=> //; split=> //.
  exact: real_power_monotone (hu0 x) hx hq.
have h := heq horder.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ h)=> x [z [hz hz']].
have hpowers : (real_power (u x) q)%:E=(real_power (v x) q)%:E.
  have hzu : (real_power (u x) q)%:E=z := hz.
  have hzv : (real_power (v x) q)%:E=z := hz'.
  by rewrite hzu hzv.
have hepower := EFin_inj hpowers.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -(real_power_order_embedding (hu0 x) (hv0 x) hq) hepower; exact: lexx.
- rewrite -(real_power_order_embedding (hv0 x) (hu0 x) hq) hepower; exact: lexx.
Qed.

(** Source for [positive_finite_lp_norm_strict_order]: strict increase of
    tau under Federer's order on U, 2.5.7, p. 99 The strictly ordered locus
    may have infinite positive measure. *)
Theorem positive_finite_lp_norm_strict_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : R) (u v : X -> R) :
  total_scalar_lp mu q%:E u -> total_scalar_lp mu q%:E v ->
  (forall x, (0 <= u x)%R) -> (forall x, (0 <= v x)%R) ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  0 < mu [set x | (u x < v x)%R] ->
  (finite_total_scalar_lp_norm mu q%:E u < finite_total_scalar_lp_norm mu q%:E v)%R.
Proof.
move=> hu hv hu0 hv0 huv hstrict.
have hle := @positive_finite_lp_norm_almost_order R X mu hm q u v hu hv hu0 hv0 huv.
rewrite lt_neqAle hle andbT; apply/eqP=> he.
have heq := @positive_finite_lp_equal_norm_almost_equal R X mu hm q u v hu hv hu0 hv0 huv he.
have hz : mu [set x | (u x < v x)%R]=0.
  apply: (@measure_null_subset R X mu hm _ _ _ heq)=> x hx heuv.
  change (is_true (u x < v x)%R) in hx.
  by rewrite heuv ltxx in hx.
by rewrite hz ltxx in hstrict.
Qed.
