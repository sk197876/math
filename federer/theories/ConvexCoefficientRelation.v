(** Federer (1969), 1.8.1, p. 38: supporting linear dependence step in the
    bound on the number of simple summands. The following elementary lemmas
    are local proofs, not separately stated claims of either source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import LinearBasis FiniteIndependence FiniteBasisComparison
  FiniteCoordinates FiniteDimension Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [oversized_family_relation]: Federer 1.8.1,
    p. 38, supporting coefficient reduction: more vectors than the
    dimension have a nontrivial vanishing linear combination. *)
Lemma oversized_family_relation (R : fieldType) (V : lmodType R)
    d (e : 'I_d -> V) (he : is_basis e) n (u : 'I_n -> V) :
  (d < n)%N -> exists b : 'I_n -> R,
    (\sum_i b i *: u i = 0) /\ exists i, b i != 0.
Proof.
move=> hdn.
have hn : ~ finite_independent u.
  move=> hu; have hh := @finite_independent_dimension R (finite_basis_vect he) n u hu.
  rewrite finite_basis_dimension card_ord in hh.
  by move: (leq_ltn_trans hh hdn); rewrite ltnn.
apply: contrapT => hnone; apply: hn => b hb i.
apply: contrapT => hi; apply: hnone.
exists b; split; first exact hb.
exists i; apply/eqP=> hbi; exact: hi hbi.
Qed.

(** Source for [nonnegative_total_positive_entry]: Federer
    1.8.1, p. 38, supporting coefficient elimination: a nonzero
    real family with nonnegative sum has a positive entry. *)
Lemma nonnegative_total_positive_entry (R : realFieldType) (I : finType)
    (b : I -> R) : 0 <= \sum_i b i -> (exists i, b i != 0) ->
    exists i, 0 < b i.
Proof.
move=> hsum [j hj]; apply: contrapT => hnone.
have hb i : b i <= 0.
  case: (leP (b i) 0) => // hi; exfalso; apply: hnone; by exists i.
have hz : \sum_i b i = 0.
  apply/eqP; rewrite eq_le; apply/andP; split=> //.
  apply: sumr_le0 => i _; exact: hb.
have hneg i (_ : true) : 0 <= -b i by rewrite oppr_ge0.
have hsumneg : \sum_i -b i = 0 by rewrite sumrN hz oppr0.
have hbj := @psumr_eq0P R I (fun _ => true) (fun i => -b i) hneg hsumneg j isT.
by move: hj; rewrite -(oppr_eq0 (b j)) hbj eqxx.
Qed.

(** Source for [oriented_family_relation]: Federer 1.8.1,
    p. 38, supporting choice of a dependence relation with nonnegative
    total coefficient. Subtracting a nonnegative multiple then cannot
    increase the total weight of a convex combination. *)
Theorem oriented_family_relation (R : realFieldType) (V : lmodType R)
    d (e : 'I_d -> V) (he : is_basis e) n (u : 'I_n -> V) :
  (d < n)%N -> exists b : 'I_n -> R,
    (\sum_i b i *: u i = 0) /\ 0 <= \sum_i b i /\ exists i, 0 < b i.
Proof.
move=> hdn; have [a [ha hne]] := @oversized_family_relation R V d e he n u hdn.
have [hs|hs] := leP 0 (\sum_i a i).
- exists a; split=> //; split=> //; exact: nonnegative_total_positive_entry hs hne.
- exists (fun i => -a i); split.
  + under eq_bigr do rewrite scaleNr.
    by rewrite sumrN ha oppr0.
  + have hb : 0 <= \sum_i -a i by rewrite sumrN oppr_ge0; exact: ltW hs.
    split=> //; apply: nonnegative_total_positive_entry hb _.
    have [i hi] := hne; exists i; by rewrite oppr_eq0.
Qed.
