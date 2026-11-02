(** Supporting set-theoretic reindexing for the continued-fraction
    comparison in Federer (1969), 2.2.9, p. 65. A bijection between natural
    quadruples and natural indices permits four digits per tree level. This
    is not an additional statement attributed to Federer. The source
    sequence is still the ordinary positive-integer sequence of 2.2.6, p.
    63. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_natural_quadrupling]: supporting inverse laws
    for the four-digit regrouping used with Federer 2.2.9,
    p. 65. The encoding is specified abstractly. *)
Record is_natural_quadrupling
    (encode : (nat * nat) * (nat * nat) -> nat)
    (decode : nat -> (nat * nat) * (nat * nat)) : Prop := {
  natural_quadrupling_encodeK : cancel encode decode;
  natural_quadrupling_decodeK : cancel decode encode
}.
