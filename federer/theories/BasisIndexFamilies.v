(** Federer (1969), 1.6.5, pp. 25-26, supporting adapted-basis
    construction for the spanning argument. Enumerating each
    original basis index once gives another basis. The proof uses
    the abstract basis criterion and dual functionals, and does
    not inspect any exterior-algebra construction. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [basis_index_family]: Federer 1.6.5, pp. 25-26,
    supporting change to an adapted basis. Reindexing a finite
    basis along an injective, surjective index family gives a
    basis; the two cardinalities need not be identified in advance. *)
Theorem basis_index_family (K : fieldType) (V : lmodType K) n
  (e : 'I_n -> V) (he : is_basis e) m (q : 'I_m -> 'I_n) :
  injective q -> (forall i, exists j, q j = i) -> is_basis (fun i => e (q i)).
Proof.
move=> hi hs; apply: finite_basis_criterion.
- apply: (@finite_independent_separating K 'I_m V (fun i => e (q i))
    (fun i => hom_as_linear (dual_basis he (q i)))) => i j.
  change (dual_basis he (q i) (e (q j)) = if i == j then 1 else 0).
  by rewrite dual_basisE (inj_eq hi) eq_sym.
- change (forall v, in_finite_span (fun i => e (q i)) v).
  apply: (basis_induction he).
  + exact: in_finite_span_zero.
  + move=> x y; exact: in_finite_span_add.
  + move=> c x; exact: in_finite_span_scale.
  + move=> i; have [j <-] := hs i; exact: finite_span_generator.
Qed.

(** Source for [basis_index_sequence]: Federer 1.6.5, pp. 25-26,
    supporting adapted-basis construction. It suffices that the
    sequence of indices be unique and contain every original index. *)
Theorem basis_index_sequence (K : fieldType) (V : lmodType K) n
  (e : 'I_n -> V) (he : is_basis e) m (q : 'I_m -> 'I_n) :
  uniq [seq q i | i <- enum 'I_m] ->
  (forall i, i \in [seq q j | j <- enum 'I_m]) -> is_basis (fun i => e (q i)).
Proof.
move=> hu hc; apply: (@basis_index_family K V n e he m q).
- have hi : injective (tnth [tuple q i | i < m]) by apply/tuple_uniqP.
  move=> i j hij; apply: hi; by rewrite !tnth_mktuple.
- move=> i; have /mapP [j _ hj] := hc i; by exists j.
Qed.

(** Source for [index_block_family]: Federer 1.6.5, pp. 25-26,
    supporting adapted-basis construction. Definition of the
    ordinal-indexed family associated with a finite list. *)
Definition index_block_family (T : Type) (s : seq T) : 'I_(size s) -> T := tnth (@Tuple (size s) T s (eqxx (size s))).
Arguments index_block_family {T} s _.

(** Source for [index_block_sequence]: Federer 1.6.5, pp. 25-26,
    supporting adapted-basis construction. The indexed family
    recovers the original ordered list exactly. *)
Lemma index_block_sequence (T : Type) (s : seq T) :
  [seq index_block_family s i | i <- enum 'I_(size s)] = s.
Proof. exact: map_tnth_enum. Qed.

(** Source for [four_block_basis]: Federer 1.6.5, pp. 25-26,
    supporting basis partition into missing, first-only, common
    and second-only factors. A unique exhaustive concatenation
    of these index lists is an actual basis of the ambient space. *)
Theorem four_block_basis (K : fieldType) (V : lmodType K) n
  (e : 'I_n -> V) (he : is_basis e) (D A B C : seq 'I_n) :
  uniq (D ++ A ++ B ++ C) -> (forall i, i \in D ++ A ++ B ++ C) ->
  is_basis (concatenate_family (fun i => e (index_block_family D i))
    (concatenate_family (fun i => e (index_block_family A i))
      (concatenate_family (fun i => e (index_block_family B i))
        (fun i => e (index_block_family C i))))).
Proof.
move=> hu hc.
pose q := concatenate_family (index_block_family D)
  (concatenate_family (index_block_family A)
    (concatenate_family (index_block_family B) (index_block_family C))).
have hq : [seq q i | i <- enum 'I_(size D+(size A+(size B+size C)))] = D ++ A ++ B ++ C.
  by rewrite /q !concatenate_family_sequence !index_block_sequence.
have hb : is_basis (fun i => e (q i)).
  apply: (@basis_index_sequence K V n e he _ q); by rewrite hq.
apply: basis_congr _ hb => i.
case: (split_ordP i) => [j ->|j ->]; rewrite /q ?concatenate_family_l ?concatenate_family_r //.
case: (split_ordP j) => [k ->|k ->]; rewrite ?concatenate_family_l ?concatenate_family_r //.
by case: (split_ordP k) => [l ->|l ->]; rewrite ?concatenate_family_l ?concatenate_family_r.
Qed.

(** Source for [mapped_index_block_sequence]: Federer 1.6.5,
    pp. 25-26, supporting adapted-basis construction. Mapping an
    indexed block through the original basis recovers exactly
    the corresponding ordered vector list. *)
Lemma mapped_index_block_sequence (I T : Type) (e : I -> T) (s : seq I) :
  [seq e (index_block_family s i) | i <- enum 'I_(size s)] = [seq e i | i <- s].
Proof. by rewrite (map_comp e (index_block_family s)) index_block_sequence. Qed.
