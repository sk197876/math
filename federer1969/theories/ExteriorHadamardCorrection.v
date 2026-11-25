(** Federer (1969), 1.7.5, p. 32, equality after the product-of-squares
    estimate: the printed equivalence omits zero factors. The local May 1987
    erratum has no entry correcting this sentence. The counterexample below
    verifies the missing zero-factor case. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerExterior ExteriorNorm
  ExteriorProductFactors ExteriorGrading FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hadamard_zero_factor_counterexample]: Federer 1.7.5, p. 32,
    local counterexample to the unqualified printed equality criterion. The
    family (0,u,u), where u is a unit vector, attains equality but is not
    mutually orthogonal. *)
Theorem hadamard_zero_factor_counterexample (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u = 1) :
  exterior_norm h2 hB (e_lambda (@idfun V) [tuple 0; u; u]) =
    inner_norm hB 0 * inner_norm hB u * inner_norm hB u /\
  ~ (forall i j : 'I_3, i != j ->
    B (tnth [tuple 0; u; u] i) (tnth [tuple 0; u; u] j) = 0).
Proof.
split.
- have hz : e_lambda (@idfun V) [tuple 0; u; u] = 0.
    apply: (@exterior_product_zero_entry R V V idfun 3 [tuple 0; u; u] 0) => //.
    by rewrite in_cons eqxx.
  by rewrite hz exterior_norm_zero inner_norm0 !mul0r.
- move=> ho.
  have hij : (lift (ord0 : 'I_3) (ord0 : 'I_2)) != (ord_max : 'I_3) by [].
  have hh := ho _ _ hij.
  change (B u u = 0) in hh.
  by move: (oner_neq0 R); rewrite -hu hh eqxx.
Qed.
