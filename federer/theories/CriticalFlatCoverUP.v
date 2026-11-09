(** Federer (1969), 3.4.2(7), p. 311: independent laws for the
    countable family of compact flat pieces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations RealNormUP
  CriticalFlatPiecesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_critical_flat_cover]: the sequence of pairs
    in 3.4.2(7), p. 311. Every pair belongs to the original Ψ class,
    and the union of its compact sets is exactly C. Existence must
    be proved from the manifold and relative closedness hypotheses. *)
Record is_critical_flat_cover (R:realType) m d (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:G (R_n R m) d) mu
    (S C:set (R_n R m)) k (T G:nat->set (R_n R m)):Prop:={
  (** Source for [critical_flat_cover_pieces]: every original pair
      is in Ψ(S,C,k), 3.4.2(7), p. 311. *)
  critical_flat_cover_pieces:forall j,is_critical_flat_piece hNY Z mu S C k (T j) (G j);
  (** Source for [critical_flat_cover_union]: C is exactly the union
      of the original compact pieces, 3.4.2(7), p. 311. *)
  critical_flat_cover_union:C=\bigcup_j G j
}.
