(** Federer (1969), 2.5.5, p. 97, applies 2.4.12, p. 87, to pass from the
    two integral errors to convergence in measure. These scalar adapters
    apply the same superlevel estimate with exponent one and use the proved
    characteristic-integral comparison, without a separate construction of
    L1 spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology CountableOrderIntervals PartialFunctionUP PartialFunctionBasic
  PartialNormedArithmetic FunctionLatticeUP SummableRealFunctionUP RealTotalCharacteristicBounds
  MeasureUP MeasureIntegralUP MeasurableFunctionUP MeasureGauge MeasureConvergenceUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_absolute_error_superlevel_measurable]: supporting
    superlevel measurability for the use of 2.4.12 in Federer 2.5.5, p. 97 *)
Lemma real_total_absolute_error_superlevel_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : X -> R) (a : \bar R) (e : R) :
  is_measure_integral mu (real_total_integrand (fun x => `|f x-g x|%R)) a ->
  measure_measurable mu [set x | (e < `|f x-g x|)%R].
Proof.
move=> hi.
have he : partial_function_preimage (real_total_integrand (fun x => `|f x-g x|%R))
    [set y : extended_real_line R | e%:E < y]=[set x | (e < `|f x-g x|)%R].
  apply/seteqP; split.
  - move=> x [y [hy hb]]; have hv := (real_total_integrand_graph _ x y).1 hy.
    change (is_true (e%:E < y)) in hb.
    by move: hb; rewrite -hv lte_fin.
  - move=> x hx; exists (`|f x-g x|%R)%:E; split; first by apply/real_total_integrand_graph.
    change (is_true (e%:E < (`|f x-g x|%R)%:E)); by rewrite lte_fin.
rewrite -he; apply: (measurable_function_open_preimage hi.1).
exact: order_strict_upper_ray_open.
Qed.

(** Source for [real_total_l1_error_gauge_bound]: quantitative exponent-one
    estimate supporting Federer 2.5.5, p. 97, from 2.4.12, p. 87 An
    absolute-error integral at most e squared gives gauge at most e. *)
Lemma real_total_l1_error_gauge_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) (a e : R) :
  (0 < e)%R -> is_measure_integral mu (real_total_integrand (fun x => `|f x-g x|%R)) a%:E ->
  (a <= e*e)%R -> measure_normed_distance mu (fun x : R^o => `|x|%R)
    (partial_function_total f) (partial_function_total g) <= e%:E.
Proof.
move=> he hi ha; pose S := [set x | (e < `|f x-g x|)%R].
have hS : measure_measurable mu S := @real_total_absolute_error_superlevel_measurable R X mu f g a%:E e hi.
have hp : function_nonnegative (fun x => `|f x-g x|%R) by move=> x; exact: normr_ge0.
have hprod := @real_total_integral_level_lower_bound R X mu hm S _ a%:E e hS he hi hp
  (fun x hx => ltW hx).
have haa : a%:E <= e%:E * e%:E by rewrite -EFinM lee_fin.
have hb := le_trans hprod haa.
have hmS : mu S <= e%:E by move: hb; rewrite lee_pmul2l ?fin_numE ?lte_fin //.
apply: measure_gauge_bound; split; first by rewrite lee_fin; exact: ltW he.
suff hset : partial_norm_superlevel (fun x : R^o => `|x|%R)
    (@partial_vector_subtract R X R^o (partial_function_total f) (partial_function_total g)) e%:E=S.
  by rewrite hset.
apply/seteqP; split.
- move=> x [z [hz hn]].
  have [u [v [hu [hv hzv]]]] := (partial_vector_subtract_graph _ _ x z).1 hz.
  have hu' : f x=u := hu; have hv' : g x=v := hv.
  change (is_true (e%:E < (`|z|%R)%:E)) in hn.
  by move: hn; rewrite hzv -hu' -hv' lte_fin.
- move=> x hx; exists (f x-g x)%R; split; last by change (is_true (e%:E < (`|f x-g x|%R)%:E)); rewrite lte_fin.
  apply/partial_vector_subtract_graph; exists (f x),(g x); by split=> //; split.
Qed.

(** Source for [real_total_l1_converges_in_measure]: exact implication used
    twice in Federer 2.5.5, p. 97 Total mass may be infinite. *)
Theorem real_total_l1_converges_in_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> R) (g : X -> R) (a : nat -> R) :
  (forall n, is_measure_integral mu (real_total_integrand (fun x => `|f n x-g x|%R)) (a n)%:E) ->
  extended_order_limit (fun n => (a n)%:E) 0 ->
  converges_in_measure mu (fun x : R^o => `|x|%R)
    (fun n => partial_function_total (f n)) (partial_function_total g).
Proof.
move=> hi hl e he; pose d := (e/2)%R.
have hd : (0 < d)%R by rewrite /d divr_gt0 // ltr0n.
have hdd : 0 < (d*d)%R%:E by rewrite lte_fin mulr_gt0.
have [K hK] := hl.2 _ hdd; exists K=> n hn.
have hb : (a n <= d*d)%R by apply: ltW; have := hK n hn; rewrite lte_fin.
have hg := @real_total_l1_error_gauge_bound R X mu hm (f n) g (a n) d hd (hi n) hb.
apply: le_lt_trans hg _; rewrite lte_fin /d ltr_pdivrMr //.
by rewrite mulr_natr -{1}(addr0 e) ltrD2l.
Qed.
