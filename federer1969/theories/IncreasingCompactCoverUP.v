(** Federer (1969), 3.4.8(5), p. 328:
    countable compact covers of the germ ring and
    its ideals support the original Borel assertions.
    These independent laws specify the auxiliary covers;
    no Borel or stratification conclusion is assumed. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_increasing_compact_cover]: an auxiliary
    increasing countable compact cover, supporting the
    countable compact unions in 3.4.8(5), p. 328.
    Increasingness permits one common index for finite
    families and changes none of the original sets. *)
Record is_increasing_compact_cover (T:topologicalType) (S:set T)
    (K:nat->set T):Prop:={
  (** Source for [increasing_compact_cover_compact]: each
      cover member is compact, supporting 3.4.8(5), p. 328. *)
  increasing_compact_cover_compact:forall n,compact (K n);
  (** Source for [increasing_compact_cover_contained]: cover
      members lie in the original set, supporting
      3.4.8(5), p. 328. *)
  increasing_compact_cover_contained:forall n,K n `<=` S;
  (** Source for [increasing_compact_cover_monotone]: a larger
      auxiliary index retains every member, supporting the
      finite products in 3.4.8(5), p. 328. *)
  increasing_compact_cover_monotone:forall m n,(m<=n)%N ->K m `<=` K n;
  (** Source for [increasing_compact_cover_covers]: every
      original point lies in a cover member, supporting
      the exact union in 3.4.8(5), p. 328. *)
  increasing_compact_cover_covers:forall x,S x ->exists n,K n x
}.
