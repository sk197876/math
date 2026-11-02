(** Federer (1969), 1.8.1, p. 38: supporting bound on the number of
    summands. its proof cites a general convex-body result. Here coefficient
    elimination is proved locally. Nonnegative weights of total at most one
    permit the empty sum in dimension zero. For a radial set containing zero
    this gives the compact hull parametrisation needed by the printed mass
    argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import LinearBasis ConvexCoefficientRelation ConvexCoefficientElimination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Reduction.
Variable R : realFieldType.
Variable V : lmodType R.
Variable d : nat.
Variable e : 'I_d -> V.
Hypothesis he : is_basis e.
Variable S : set V.

(** Source for [subconvex_dimension_reduction]: Federer 1.8.1,
    p. 38, supporting finite-dimensional reduction of combinations.
    A combination of points of S with nonnegative weights summing to
    at most one admits such a representation with at most d points.
    No convexity, radiality, or nonemptiness of S is needed for this step. *)
Theorem subconvex_dimension_reduction n (u : 'I_n -> V) (a : 'I_n -> R) :
  (forall i, S (u i)) -> (forall i, 0 <= a i) -> (\sum_i a i <= 1) ->
  exists k, exists v : 'I_k -> V, exists c : 'I_k -> R,
    (k <= d)%N /\ (forall i, S (v i)) /\ (forall i, 0 <= c i) /\
    (\sum_i c i <= 1) /\ \sum_i a i *: u i = \sum_i c i *: v i.
Proof.
elim: n u a => [|n ih] u a hu ha hsum.
- exists 0%N, u, a; repeat split=> //.
have [hnd|hdn] := leqP n.+1 d.
- exists n.+1, u, a; repeat split=> //.
have [b [hb [hsb hpos]]] := @oriented_family_relation R V d e he n.+1 u hdn.
have [t [j [ht [hc [hcj hsc]]]]] := @convex_coefficient_elimination R
  (Finite.clone 'I_n.+1 _) a b ha hsb hpos.
pose c i := a i-t*b i.
pose v (i : 'I_n) := u (lift j i).
pose w (i : 'I_n) := c (lift j i).
have hj0 : c j = 0 := hcj.
have hv i : S (v i) := hu (lift j i).
have hw i : 0 <= w i := hc (lift j i).
have hsplit : (\sum_i c i) = c j + \sum_i w i.
  by rewrite (bigD1_ord j).
have htotal : \sum_i w i <= 1.
  have h := le_trans hsc hsum.
  change (is_true (\sum_i c i <= 1)) in h.
  by rewrite hsplit hj0 add0r in h.
have hsplitv : (\sum_i c i *: u i) = c j *: u j + \sum_i w i *: v i.
  by rewrite (bigD1_ord j).
have hvalue : \sum_i a i *: u i = \sum_i w i *: v i.
  have h := @weighted_relation_adjustment R (Finite.clone 'I_n.+1 _) V a b u t hb.
  change (\sum_i c i *: u i = \sum_i a i *: u i) in h.
  rewrite hsplitv hj0 scale0r add0r in h; exact: esym h.
have [k [z [q [hkd [hz [hq [hqs hqv]]]]]]] := ih v w hv hw htotal.
exists k, z, q; repeat split=> //; exact: eq_trans hvalue hqv.
Qed.
End Reduction.
