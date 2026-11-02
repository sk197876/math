(** Federer (1969), 2.5.13, pp. 106–107: choose a finite constant bounding
    the absolute functional values on a positive order interval, using
    2.5.6, pp. 97–98, then rescale it by the uniform error. No Daniell
    continuity is assumed in these supporting steps, since that is the
    conclusion to be proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP LatticeAdditiveFunctional FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lattice_positive_interval_absolute_bound]: the
    finite bound c in Federer 2.5.13, p. 106,
    justified by 2.5.6, pp. 97–98. An explicit
    nonnegative upper bound suffices; no supremum is chosen. *)
Lemma lattice_positive_interval_absolute_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_lattice_additive_functional L A) (f : X -> R) :
  L f -> (exists b, forall k, lattice_positive_order_interval L f k -> A k <= b) ->
  exists c, 0 <= c /\ forall k, lattice_positive_order_interval L f k -> `|A k| <= c.
Proof.
move=> hf [b hb]; exists (`|b|+`|b-A f|); split; first exact: addr_ge0 (normr_ge0 _) (normr_ge0 _).
move=> k hk; rewrite ler_norml; apply/andP; split.
- rewrite lerNl; apply: le_trans (@lattice_additive_negative_order_bound R X L A hL hA f b hf hb k hk) _.
  apply: le_trans (ler_norm _) _; by rewrite lerDr normr_ge0.
- apply: le_trans (hb k hk) _; apply: le_trans (ler_norm _) _; by rewrite lerDl normr_ge0.
Qed.

(** Source for [lattice_scaled_positive_interval_bound]: the estimate
    |mu(g-h_n)| <= epsilon c in Federer 2.5.13, p. 107 The positive scalar
    is divided out inside the same lattice. *)
Lemma lattice_scaled_positive_interval_bound (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_linear_functional_on_functions L A) (f k : X -> R) (e c : R) :
  0 < e -> L k -> function_nonnegative k -> (forall x, k x <= e*f x) ->
  (forall q, lattice_positive_order_interval L f q -> `|A q| <= c) -> `|A k| <= e*c.
Proof.
move=> he hk hp hb hc; pose q x := e^-1*k x.
have he0 : e != 0 by rewrite gt_eqF.
have hei : 0 <= e^-1 by rewrite invr_ge0; exact: ltW he.
have hqi : lattice_positive_order_interval L f q.
  split; first exact (@function_lattice_scale R X L hL e^-1 k hei hk).
  split=> x; first exact: mulr_ge0 hei (hp x).
  have h := ler_wpM2l hei (hb x).
  by rewrite mulrA mulVf // mul1r in h.
have hv : A k=e*A q by rewrite (hA.2 e^-1 k hk) mulrA mulfV // mul1r.
rewrite hv normrM (ger0_norm (ltW he)); exact (ler_wpM2l (ltW he) (hc q hqi)).
Qed.
