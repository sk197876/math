(** Federer (1969), 2.4.19, p. 91: the finite-image Jensen inequality. This
    supporting epigraph argument derives finite Jensen directly from binary
    convexity; it is not an additional separation theorem attributed to the
    book. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex ConvexFunctionUP ConvexTranslatedCombinations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_function_epigraph]: supporting epigraph specification
    for the finite-image case of Federer 2.4.19, p. 91 *)
Definition convex_function_epigraph (R : realFieldType) (V : lmodType R)
    (C : set V) (F : V -> R) : set (V * R) :=
  [set p | C p.1 /\ F p.1 <= p.2].

(** Source for [convex_function_epigraph_convex]: supporting
    consequence of the convex-function hypothesis in Federer 2.4.19,
    p. 91. The proof uses only its binary inequality. *)
Lemma convex_function_epigraph_convex (R : realFieldType) (V : lmodType R)
    (C : set V) (F : V -> R) :
  is_real_convex_function_on C F ->
  @is_inner_convex R (GRing.Lmodule.clone R (V * R^o)%type _) (convex_function_epigraph C F).
Proof.
move=> [hC hF] [x a] [y b] [hx hax] [hy hby] t ht ht1; split.
- exact: hC x y hx hy t ht ht1.
- change (F ((1-t) *: x+t *: y) <= (1-t) * a+t * b).
  apply: le_trans (hF x y hx hy t ht ht1) _.
  have h1t : 0 <= 1-t by rewrite subr_ge0.
  exact: (lerD (ler_wpM2l h1t hax) (ler_wpM2l ht hby)).
Qed.

(** Source for [finite_convex_jensen]: algebraic finite-combination
    inequality underlying the first case of Federer 2.4.19, p. 91 The
    weighted mean belongs to C, so evaluating F there is justified. Empty
    sums cannot have total weight one. *)
Theorem finite_convex_jensen (R : realFieldType) (V : lmodType R)
    (C : set V) (F : V -> R) n (u : 'I_n -> V) (a : 'I_n -> R) :
  is_real_convex_function_on C F -> (forall i, C (u i)) ->
  (forall i, 0 <= a i) -> \sum_i a i= 1 ->
  C (\sum_i a i *: u i) /\ F (\sum_i a i *: u i) <= \sum_i a i * F (u i).
Proof.
case: n u a=> [|n] u a hF hu ha hs.
- by move: hs; rewrite big_ord0; move/eqP; rewrite eq_sym oner_eq0.
pose v i : (GRing.Lmodule.clone R (V * R^o)%type _) := (u i,F (u i)).
have hv i : convex_function_epigraph C F (v i) by split; [exact: hu | exact: lexx].
have hh := @convex_weighted_sum R (GRing.Lmodule.clone R (V * R^o)%type _)
  (convex_function_epigraph C F) (v ord0) n.+1 v a
  (convex_function_epigraph_convex hF) (hv ord0) hv ha hs.
change (C (\sum_i a i *: u i) /\ F (\sum_i a i *: u i) <= \sum_i a i * F (u i)).
have he : \sum_i a i *: v i=(\sum_i a i *: u i,\sum_i a i * F (u i)).
  apply: injective_projections; rewrite !linear_sum /=; apply: eq_bigr=> i _; by [].
by rewrite he in hh.
Qed.

(** Source for [finite_sequence_convex_jensen]: finite-list form of the
    finite-image case of Federer 2.4.19, p. 91 Repeated labels cause no
    problem because each carries its own weight. *)
Theorem finite_sequence_convex_jensen (R : realFieldType) (V : lmodType R)
    (C : set V) (F : V -> R) (s : seq V) (a : V -> R) :
  is_real_convex_function_on C F -> (forall y, y \in s -> C y) ->
  (forall y, y \in s -> 0 <= a y) -> (\sum_(y <- s) a y)= 1 ->
  C (\sum_(y <- s) a y *: y) /\ F (\sum_(y <- s) a y *: y) <= \sum_(y <- s) a y * F y.
Proof.
move=> hF hC ha hs.
have hC' (i : 'I_(size s)) : C (nth 0 s i) := hC _ (mem_nth 0 (ltn_ord i)).
have ha' (i : 'I_(size s)) : 0 <= a (nth 0 s i) := ha _ (mem_nth 0 (ltn_ord i)).
have hs' : (\sum_(i < size s) a (nth 0 s i))= 1.
  by rewrite (big_nth 0) big_mkord in hs.
have hh := @finite_convex_jensen R V C F (size s) (fun i => nth 0 s i)
  (fun i => a (nth 0 s i)) hF hC' ha' hs'.
have heV : (\sum_(y <- s) a y *: y)=(\sum_(i < size s) a (nth 0 s i) *: nth 0 s i).
  by rewrite (big_nth 0) big_mkord.
have heF : (\sum_(y <- s) a y * F y)=(\sum_(i < size s) a (nth 0 s i) * F (nth 0 s i)).
  by rewrite (big_nth 0) big_mkord.
by rewrite heV heF.
Qed.

(** Source for [finite_mass_normalized_jensen]: normalization by the finite
    positive total measure in Federer 2.4.19, p. 91 *)
Theorem finite_mass_normalized_jensen (R : realFieldType) (V : lmodType R)
    (C : set V) (F : V -> R) (s : seq V) (a : V -> R) (m : R) :
  is_real_convex_function_on C F -> (forall y, y \in s -> C y) ->
  (forall y, y \in s -> 0 <= a y) -> 0 < m -> (\sum_(y <- s) a y)=m ->
  C (m^-1 *: (\sum_(y <- s) a y *: y)) /\
  F (m^-1 *: (\sum_(y <- s) a y *: y)) <= (\sum_(y <- s) a y * F y)/m.
Proof.
move=> hF hC ha hm hs.
have hm0 : m != 0 by rewrite gt_eqF.
have hw y : y \in s -> 0 <= a y/m by move=> hy; exact: divr_ge0 (ha y hy) (ltW hm).
have hsum : (\sum_(y <- s) a y/m)= 1 by rewrite -mulr_suml hs divff.
have hh := @finite_sequence_convex_jensen R V C F s (fun y => a y/m) hF hC hw hsum.
have he : (\sum_(y <- s) (a y/m) *: y)=m^-1 *: (\sum_(y <- s) a y *: y).
  rewrite scaler_sumr; apply: eq_bigr=> y _; by rewrite scalerA mulrC.
have hev : (\sum_(y <- s) (a y/m) * F y)=(\sum_(y <- s) a y * F y)/m.
  rewrite mulr_suml; apply: eq_bigr=> y _; by rewrite mulrAC.
by rewrite he hev in hh.
Qed.
