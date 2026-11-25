(** Federer (1969), 2.7.16, printed p. 139, example (6): the integrand p |->
    |(Lambda_m p) xi|^t of "(int |(Lambda_m p) xi|^t dtheta*_{n,m} p)^{1/t}
    = beta_t(n, m) . |xi|" is a continuous function of p. Here V and U are
    spaces with inner products B and C, V has a finite basis b, and Hom(V,
    U) carries the topology of the inner product of 1.7.9, p. 35
    (HomSpaceTopology.v). For a simple m-vector xi = v_1 wedge ... wedge v_m
    of V (1.6.1, p. 23) one has (Lambda_m p) xi = p(v_1) wedge ... wedge
    p(v_m) (1.3.1, p. 14), and the permutation formula of 1.7.5, pp. 31-32,
    expresses |(Lambda_m p) xi|^2 as a finite sum of signed products of the
    numbers p(v_i) . p(v_j). Each of these is continuous in p by
    polarisation, since p |-> |p(x)| is continuous. The power |(Lambda_m p)
    xi|^t = (|(Lambda_m p) xi|^2)^{t/2} is then continuous by
    RealPowerContinuity.v. Federer uses this continuity tacitly. neither
    treats continuity in p. The local erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm boolp classical_sets reals
  topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import ring.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis
  TensorUP Hom HomInner HomSpaceTopology TopologicalProductMaps RealMetricBackground RealPower
  RealPowerContinuity ExteriorGrading ExteriorMaps FiniteExteriorPowers InnerExterior
  InnerExteriorProducts InnerExteriorPositivity ExteriorNorm AssociatedSubspace SimpleElementary
  ExteriorAlgebra AlgebraUP GradedComponents GradedAlgebra Bilinear InversionCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_power_map_e_lambda]: "(Lambda_m f)(v_1 wedge ...
    wedge v_m) = f(v_1) wedge ... wedge f(v_m)", Federer 1.3.1, p. 14,
    for an indexed family of vectors; supporting (Lambda_m p) xi in
    2.7.16, p. 139. Supporting lemma. *)
Lemma exterior_power_map_e_lambda (K : fieldType) (V U : lmodType K) (I : choiceType)
    (f : {linear V -> U}) m (e : I -> V) (t : m.-tuple I) :
  exterior_power_map f m (e_lambda e t) = e_lambda (f \o e) t.
Proof.
apply: val_inj.
change (exterior_algebra_map f (component_val (e_lambda e t)) = component_val (e_lambda (f \o e) t)).
by rewrite !e_lambdaE exterior_algebra_map_word -map_comp.
Qed.

Section MapNormContinuity.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Variables V U : lmodType R.
Variables (B : V -> V -> R) (C : U -> U -> R).
Hypotheses (hB : is_inner_product B) (hC : is_inner_product C).
Variables (n : nat) (b : 'I_n -> V).
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hC hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation UT := (inner_metric_space hC).

(** Source for [hom_value_norm_continuous]: p |-> |p(x)| is continuous
    on Hom(V, U), supporting the continuity of the integrand of Federer
    2.7.16, p. 139; the evaluation is continuous by 1.7.9, p. 35.
    Supporting lemma. *)
Lemma hom_value_norm_continuous (x : V) :
  continuous (fun p : H => inner_norm hC ((p : Hom V U) x) : real_line_metric R).
Proof.
have he : continuous (fun p : H => ((p : Hom V U) x : UT)).
  move=> p.
  have hp : continuous (fun q : H => (q, (x : VT))).
    by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
  exact: (continuous_comp (hp p) (@hom_evaluation_continuous R V U B C hB hC n b hb (p, (x : VT)))).
move=> p; apply: (continuous_comp (he p)).
have hn := @norm_continuous R UT ((p : Hom V U) x).
have he' : (fun y : UT => `|y|) = inner_norm hC.
  by apply: funext=> y; rewrite inner_norm_topologyE.
by rewrite -he'.
Qed.

(** Source for [hom_value_inner_continuous]: p |-> p(x) . p(y) is
    continuous on Hom(V, U), by polarisation 4 u . w = |u + w|^2 -
    |u - w|^2 (1.7.1, p. 28); supporting the continuity of the integrand
    of Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma hom_value_inner_continuous (x y : V) :
  continuous (fun p : H => C ((p : Hom V U) x) ((p : Hom V U) y) : real_line_metric R).
Proof.
have hbil := inner_bilinear hC.
have hsum (u w : U) : C (u + w) (u + w) = C u u + (C u w + C u w) + C w w.
  rewrite (bilDl hbil) !(bilDr hbil) (inner_symmetric hC w u); ring.
have hdif (u w : U) : C (u - w) (u - w) = C u u - (C u w + C u w) + C w w.
  rewrite (bilBl hbil) !(bilBr hbil) (inner_symmetric hC w u); ring.
have hpol (p : Hom V U) : C (p x) (p y) =
    (inner_norm hC (p (x + y)) ^+ 2 - inner_norm hC (p (x - y)) ^+ 2) / 4%:R.
  rewrite !inner_norm_sqr (linearD (hom_as_linear p)) (linearB (hom_as_linear p)) /=.
  rewrite ?hom_as_linearE hsum hdif.
  have h4 : (4%:R : R) != 0 by rewrite pnatr_eq0.
  by apply: (mulIf h4); rewrite divfK //; ring.
have -> : (fun p : H => C ((p : Hom V U) x) ((p : Hom V U) y)) =
    (fun p : H => (inner_norm hC ((p : Hom V U) (x + y)) * inner_norm hC ((p : Hom V U) (x + y)) -
      inner_norm hC ((p : Hom V U) (x - y)) * inner_norm hC ((p : Hom V U) (x - y))) / 4%:R).
  by apply: funext=> p; rewrite hpol !expr2.
move=> p.
have h1 := @hom_value_norm_continuous (x + y) p.
have h2' := @hom_value_norm_continuous (x - y) p.
have hc : {for p, continuous (fun q : H =>
    (inner_norm hC ((q : Hom V U) (x + y)) * inner_norm hC ((q : Hom V U) (x + y)) -
    inner_norm hC ((q : Hom V U) (x - y)) * inner_norm hC ((q : Hom V U) (x - y)) : R^o))}.
  have hf := @continuousM R H _ _ p h1 h1.
  have hg := @continuousM R H _ _ p h2' h2'.
  exact: (@continuousB R R^o H _ _ p hf hg).
exact: (@continuousM R H _ (fun _ : H => 4%:R^-1) p hc (@cst_continuous H R^o _ p)).
Qed.

(** Source for [foldr_product_continuous]: a finite product of
    continuous real functions is continuous; supporting the permutation
    formula of Federer 1.7.5, pp. 31-32, in the continuity of the
    integrand of 2.7.16, p. 139. Supporting lemma. *)
Lemma foldr_product_continuous (X : topologicalType) (I : Type) (F : I -> X -> R) (s : seq I) :
  (forall i, continuous (F i : X -> real_line_metric R)) ->
  continuous ((fun z => foldr ( *%R) 1 [seq F i z | i <- s]) : X -> real_line_metric R).
Proof.
move=> hF; elim: s => [|i s ih] /=; first exact: cst_continuous.
move=> z; exact: (@continuousM R X _ _ z (hF i z) (ih z)).
Qed.

(** Source for [exterior_map_norm_square_continuous]: for a simple
    m-vector xi of V, p |-> |(Lambda_m p) xi|^2 is continuous on
    Hom(V, U), by the permutation formula of Federer 1.7.5, pp. 31-32;
    supporting the integrand of 2.7.16, p. 139. Supporting lemma. *)
Lemma exterior_map_norm_square_continuous m (xi : exterior_power V m) :
  simple xi ->
  continuous (fun p : H =>
    exterior_norm h2 hC (exterior_power_map (hom_as_linear (p : Hom V U)) m xi) ^+ 2 : real_line_metric R).
Proof.
move=> [t ->]; rewrite tuple_product.
have -> : (fun p : H => exterior_norm h2 hC (exterior_power_map (hom_as_linear (p : Hom V U)) m
      (e_lambda (tnth t) (ord_tuple m))) ^+ 2) =
    (fun p : H => \sum_(sigma : 'S_m) FedererPermutation.index R sigma *
      foldr ( *%R) 1 [seq C ((p : Hom V U) (tnth t (sigma i))) ((p : Hom V U) (tnth t i)) |
        i <- enum 'I_m]).
  apply: funext=> p; rewrite exterior_norm_square exterior_power_map_e_lambda.
  rewrite exterior_inner_product_permutations.
  by apply: eq_bigr=> sigma _; congr (_ * foldr _ _ _); apply: eq_map=> i; rewrite /= !hom_as_linearE.
apply: (@continuous_big R^o); first exact: add_continuous.
move=> sigma _.
move=> p; apply: (@continuousM R H _ _ p); first exact: cst_continuous.
apply: (@foldr_product_continuous H 'I_m
  (fun i (q : H) => C ((q : Hom V U) (tnth t (sigma i))) ((q : Hom V U) (tnth t i)))).
move=> i; exact: hom_value_inner_continuous.
Qed.

(** Source for [exterior_map_norm_power_continuous]: for a simple
    m-vector xi of V and t > 0, p |-> |(Lambda_m p) xi|^t is continuous
    on Hom(V, U): the integrand of "(int |(Lambda_m p) xi|^t
    dtheta*_{n,m} p)^{1/t}", Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma exterior_map_norm_power_continuous m (xi : exterior_power V m) (t : R) :
  simple xi -> 0 < t ->
  continuous (fun p : H =>
    real_power (exterior_norm h2 hC (exterior_power_map (hom_as_linear (p : Hom V U)) m xi)) t
      : real_line_metric R).
Proof.
move=> hs ht.
have -> : (fun p : H => real_power (exterior_norm h2 hC
      (exterior_power_map (hom_as_linear (p : Hom V U)) m xi)) t) =
    (fun p : H => real_power (exterior_norm h2 hC
      (exterior_power_map (hom_as_linear (p : Hom V U)) m xi) ^+ 2) (t / 2)).
  apply: funext=> p; rewrite real_power_square_half //; exact: exterior_norm_nonnegative.
apply: real_power_continuous_comp; last by rewrite divr_gt0.
- exact: exterior_map_norm_square_continuous.
- move=> p; exact: sqr_ge0.
Qed.

(** Source for [exterior_map_norm_continuous]: for a simple m-vector xi
    of V, p |-> |(Lambda_m p) xi| is continuous on Hom(V, U): the
    function f(p) = |<xi, Lambda_m p>| of Federer 2.7.16, p. 140.
    Supporting lemma. *)
Lemma exterior_map_norm_continuous m (xi : exterior_power V m) :
  simple xi ->
  continuous (fun p : H =>
    exterior_norm h2 hC (exterior_power_map (hom_as_linear (p : Hom V U)) m xi) : real_line_metric R).
Proof.
move=> hs.
have -> : (fun p : H => exterior_norm h2 hC (exterior_power_map (hom_as_linear (p : Hom V U)) m xi)) =
    (fun p : H => real_power (exterior_norm h2 hC
      (exterior_power_map (hom_as_linear (p : Hom V U)) m xi)) 1).
  apply: funext=> p; rewrite real_power_one_exponent //; exact: exterior_norm_nonnegative.
exact: exterior_map_norm_power_continuous hs ltr01.
Qed.

End MapNormContinuity.
