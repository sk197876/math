(** Federer (1969), 2.2.15, pp. 70–71: the real- valued Baire functions form
    an algebra. We derive constant, additive, multiplicative, negative and
    scalar closure from pair closure and continuous postcomposition. The
    narrow pseudometric_normed_Zmodule and normed_module imports supply
    continuity of real arithmetic as scalar-topology background, not
    Baire-function mathematics. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground MetricProductBackground
  BaireFunctions BairePostcomposition BairePairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [baire_real_constant]: supporting constant
    functions in the real Baire algebra of Federer 2.2.15,
    pp. 70–71, including its zero and unit. *)
Lemma baire_real_constant (R : realType) (X : topologicalType) (c : R) :
  @is_baire_function R X [the metricType R of real_line_metric R] (fun _ => c).
Proof. apply: continuous_baire_function=> x; exact: cvg_cst. Qed.

(** Source for [baire_real_add]: direct additive closure
    in the algebra assertion of Federer 2.2.15, pp. 70–71. *)
Lemma baire_real_add (R : realType) (X : topologicalType)
    (f g : X -> real_line_metric R) :
  is_baire_function f -> is_baire_function g ->
  @is_baire_function R X [the metricType R of real_line_metric R] (fun x => f x + g x).
Proof.
move=> hf hg.
pose M := [the metricType R of real_line_metric R].
pose P := [the metricType R of metric_product M M].
pose h (p : P) : M := p.1 + p.2.
have hh : continuous h.
  change (continuous (fun p : R^o * R^o => p.1 + p.2)).
  exact: add_continuous.
exact: (@baire_continuous_postcomposition R X P M h hh (fun x => (f x,g x))
  (baire_pair_functions hf hg)).
Qed.

(** Source for [baire_real_mul]: direct multiplicative closure
    in the algebra assertion of Federer 2.2.15, pp. 70–71. *)
Lemma baire_real_mul (R : realType) (X : topologicalType)
    (f g : X -> real_line_metric R) :
  is_baire_function f -> is_baire_function g ->
  @is_baire_function R X [the metricType R of real_line_metric R] (fun x => f x * g x).
Proof.
move=> hf hg.
pose M := [the metricType R of real_line_metric R].
pose P := [the metricType R of metric_product M M].
pose h (p : P) : M := p.1 * p.2.
have hh : continuous h.
  change (continuous (fun p : R^o * R^o => p.1 * p.2)).
  move=> p; apply: cvgM; [exact: cvg_fst|exact: cvg_snd].
exact: (@baire_continuous_postcomposition R X P M h hh (fun x => (f x,g x))
  (baire_pair_functions hf hg)).
Qed.

(** Source for [baire_real_scale]: scalar closure in
    the real algebra of Federer 2.2.15, pp. 70–71,
    obtained by multiplication by a constant Baire function. *)
Lemma baire_real_scale (R : realType) (X : topologicalType)
    (f : X -> real_line_metric R) (c : R) : is_baire_function f ->
  @is_baire_function R X [the metricType R of real_line_metric R] (fun x => c * f x).
Proof. move=> hf; exact: baire_real_mul (baire_real_constant X c) hf. Qed.

(** Source for [baire_real_opp]: additive inverses in the
    real algebra of Federer 2.2.15, pp. 70–71. *)
Lemma baire_real_opp (R : realType) (X : topologicalType)
    (f : X -> real_line_metric R) : is_baire_function f ->
  @is_baire_function R X [the metricType R of real_line_metric R] (fun x => - f x).
Proof.
move=> hf; have he : (fun x => - f x) = (fun x => (-1) * f x).
  by apply: funext=> x; rewrite mulN1r.
rewrite he; exact: baire_real_scale hf.
Qed.

(** Source for [baire_real_finite_sum]: supporting finite
    sums for the simple-function approximation in Federer 2.2.15,
    p. 71. The zero-length sum is the constant zero. *)
Lemma baire_real_finite_sum (R : realType) (X : topologicalType)
    (f : nat -> X -> real_line_metric R) :
  (forall i, is_baire_function (f i)) -> forall n,
  @is_baire_function R X [the metricType R of real_line_metric R]
    (fun x => \sum_(i < n) f i x).
Proof.
move=> hf n; elim: n=> [|n ih].
- have he : (fun x => \sum_(i < 0) f i x) = (fun _ : X => 0).
    by apply: funext=> x; rewrite big_ord0.
  rewrite he; exact: baire_real_constant.
- have he : (fun x => \sum_(i < n.+1) f i x) =
      (fun x => (\sum_(i < n) f i x) + f n x).
    by apply: funext=> x; rewrite big_ord_recr.
  rewrite he; exact: baire_real_add ih (hf n).
Qed.
