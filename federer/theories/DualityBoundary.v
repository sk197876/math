(** Local corrections to Federer (1969), 1.6.3, pp. 24-25. Neither source
    restricts the output degree in its assertion that duality preserves
    simplicity. The one-dimensional examples below disprove that assertion
    for the literal empty-product convention. They are local corrections,
    not erratum entries. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors SimpleAdaptedBasis
  CovectorBoundary DualitySimplicity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simple_zero_positive]: Federer 1.6.3, p. 24,
    simplicity under duality, using the definition in 1.6.1. Supporting
    boundary fact: zero is a simple vector in every positive degree. *)
Lemma simple_zero_positive (K : fieldType) (V : lmodType K) m :
  (0 < m)%N -> simple (0 : exterior_power V m).
Proof.
move=> hm; have hs := @simple_scale K V m
  (e_lambda (fun _ : 'I_m => (0 : V)) (ord_tuple m)) 0 hm (product_simple _).
by rewrite scale0r in hs.
Qed.

(** Source for [simple_covector_zero_positive]: Federer 1.6.3,
    p. 24, simplicity under duality. Supporting boundary fact: zero
    is a simple covector in every positive degree. *)
Lemma simple_covector_zero_positive (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) m : (0 < m)%N -> simple_covector h2 (0 : A_m V K^o m).
Proof.
move=> hm; rewrite -(linear0 (@Omega_m K h2 V m)).
apply: (proj2 (simple_covector_Omega h2 _)); exact: simple_zero_positive hm.
Qed.

(** Source for [D_p_preserves_simple]: Federer 1.6.3, pp. 24-25,
    simplicity under D_p. Direct corrected assertion, including the
    zero input: the output degree must be positive. *)
Theorem D_p_preserves_simple (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : A_m V K^o n) p (hp : (p <= n)%N)
  (xi : exterior_power V p) :
  (p < n)%N -> simple xi -> simple_covector h2 (D_p volume hp xi).
Proof.
move=> hpn hs; have [->|hx] := eqVneq xi 0.
- rewrite linear0; apply: simple_covector_zero_positive; by rewrite subn_gt0.
- exact: (@D_p_simple_nonzero K h2 V n e he volume p hp xi hpn hx hs).
Qed.

(** Source for [D_upper_preserves_simple]: Federer 1.6.3, p. 24,
    simplicity under D^p. Direct corrected assertion, including zero
    input, with the positive-output-degree restriction. *)
Theorem D_upper_preserves_simple (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
  (volume : exterior_power V n) p (hp : (p <= n)%N)
  (phi : A_m V K^o p) :
  (p < n)%N -> simple_covector h2 phi -> simple (D_upper h2 volume hp phi).
Proof.
move=> hpn hs; have [->|hx] := eqVneq phi 0.
- rewrite linear0; apply: simple_zero_positive; by rewrite subn_gt0.
- exact: (@D_upper_simple_nonzero K h2 V n e he volume p hp phi hpn hx hs).
Qed.

(** Source for [empty_product_scalar]: Federer 1.6.3, pp. 24-25,
    degree-zero boundary of duality. Supporting identity: every empty
    indexed exterior product is the scalar inclusion of one. *)
Lemma empty_product_scalar (K : fieldType) (I : choiceType) (V : lmodType K)
  (e : I -> V) (t : 0.-tuple I) :
  e_lambda e t = exterior_zeroth_inclusion V 1.
Proof.
apply: val_inj.
change (component_val (e_lambda e t) = component_val (exterior_zeroth_inclusion V 1)).
by rewrite e_lambdaE zeroth_inclusion_val /exterior_scalar scale1r
  (tuple0 t) /= exterior_word_nil.
Qed.

Section Counterexamples.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable e : 'I_1 -> V.
Hypothesis he : is_basis e.
Local Notation omega := (fun i => one_form (dual_basis he i)).
Local Notation et := (e_lambda e (val (Lambda_top 1))).
Local Notation ot := (omega_lambda h2 omega (Lambda_top 1)).

(** Source for [two_not_one]: Federer 1.6.3, p. 24, degree-zero
    exception. Supporting field identity used in the counterexamples. *)
Lemma two_not_one : (1+1 : K) != 1.
Proof.
apply/eqP=> h; have h1 : (1 : K) = 0 by apply: (addrI (1 : K)); rewrite addr0.
by move: (oner_neq0 K); rewrite h1 eqxx.
Qed.

(** Source for [D_p_zero_degree_counterexample]: Federer 1.6.3,
    pp. 24-25, unrestricted simplicity assertion. Local counterexample
    in any one-dimensional space: twice the basis vector is simple,
    but its dual is the scalar 2, not the empty product 1. *)
Theorem D_p_zero_degree_counterexample :
  exists xi : exterior_power V 1, simple xi /\
    ~ simple_covector h2 (D_p ot (leqnn 1) xi).
Proof.
exists ((1+1 : K) *: et); split.
- apply: simple_scale; first by [].
  exact: indexed_product_simple.
- have ht : et = e_lambda e (val (Lambda_initial (leqnn 1))).
    by rewrite (Lambda_top_unique (Lambda_initial (leqnn 1))).
  rewrite linearZ ht.
  change (~ simple_covector h2 ((1+1 : K) *:
    D_p ot (leqnn 1) (e_lambda e (val (Lambda_initial (leqnn 1)))))).
  rewrite (@D_p_initial_basis K h2 V 1 e he 1 (leqnn 1)) expr0 scale1r omega_lambda_empty.
  rewrite /scalar_covector -linearZ -linearZ.
  change (~ simple_covector h2 (scalar_covector h2 V ((1+1)*1))).
  rewrite mulr1 scalar_covector_simple => h.
  by move: two_not_one; rewrite h eqxx.
Qed.

(** Source for [D_upper_zero_degree_counterexample]: Federer 1.6.3,
    p. 24, unrestricted simplicity assertion. Local counterexample
    for the reverse duality: twice a dual basis one-form is simple,
    but D^1 sends it to the scalar 2, which is not a simple zero-vector. *)
Theorem D_upper_zero_degree_counterexample :
  exists phi : A_m V K^o 1, simple_covector h2 phi /\
    ~ simple (D_upper h2 et (leqnn 1) phi).
Proof.
exists ((1+1 : K) *: ot); split.
- apply: simple_covector_scale; first by [].
  exact: omega_lambda_simple.
- rewrite linearZ.
  change (~ simple ((1+1 : K) *: D_upper h2 et (leqnn 1) ot)).
  rewrite (@D_upper_basis K h2 V 1 e omega he
    (@finite_dual_biorthogonal K V 1 e he)) empty_product_scalar.
  have hz : FedererInteriorSigns.N (Lambda_top 1) (top_complement (Lambda_top 1)) = 0%N.
    rewrite -[Lambda_top 1](Lambda_top_unique (Lambda_initial (leqnn 1)))
      /top_complement initial_complement_N; by [].
  rewrite hz expr0 scale1r -linearZ.
  change (~ simple (exterior_zeroth_inclusion V ((1+1)*1))).
  rewrite mulr1; exact: scalar_not_simple two_not_one.
Qed.
End Counterexamples.
