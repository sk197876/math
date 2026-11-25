(** Federer (1969), 4.1.11, p. 366: the
    original finite segment factors may have independent
    Euclidean dimensions. Whole-space factors have the
    whole original product domain, including the empty family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanBlockCoordinates EuclideanCartesianMap
  OrientedSegmentFactor OrientedRectangleDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_current_full_rectangle_family]: each
    original containing factor is its whole Euclidean
    space, the original rectangular currents in
    Federer 4.1.11, p. 366. This is a logical
    predicate, without chosen vertices or simplices. *)
Fixpoint is_current_full_rectangle_family (R:realType) (f:seq (oriented_segment_factor R)):Prop:=
  match f with
  |[::]=>True
  |a::t=>(@oriented_segment_factor_domain R a=(fun _=>True)) /\ is_current_full_rectangle_family t
  end.

(** Source for [current_full_rectangle_domain]: the original
    finite product of whole Euclidean factors has the
    full product domain, supporting Federer 4.1.11,
    p. 366. Factor dimensions remain arbitrary. *)
Lemma current_full_rectangle_domain (R:realType) (f:seq (oriented_segment_factor R)):
  is_current_full_rectangle_family f->
  @oriented_rectangle_domain R f=(fun _:R_n R (oriented_rectangle_dimension f)=>True).
Proof.
elim:f=>[|a [|b t] ih] hFull.
- by [].
- exact:hFull.1.
- move:hFull=>[hFirst hRest].
  have hTail:=ih hRest.
  apply:funext=>z;apply:propext;split=>_;first exact:Logic.I.
  change (@oriented_segment_factor_domain R a (euclidean_block_split z).1 /\
    @oriented_rectangle_domain R (b::t) (euclidean_block_split z).2).
  rewrite hFirst hTail;exact:(conj Logic.I Logic.I).
Qed.
