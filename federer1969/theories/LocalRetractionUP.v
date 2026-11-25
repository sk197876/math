(** Federer (1969), 3.1.20, p. 232, corrected by the erratum,
    p. 4, book p. 232 lines 11, 14–15: intermediate maps W_i to B
    fix B intersect W_i; they need not take values in W_i. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormRegularity RetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_partial_neighbourhood_retraction]: the corrected
    intermediate-map invariant of Federer 3.1.20, p. 232, erratum
    p. 4, book p. 232 line 11. The image lies in B, not necessarily
    B intersect W; only points of B intersect W must be fixed. *)
Record is_partial_neighbourhood_retraction (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B W:set X) (f:X->X) k : Prop := {
  (** Source for [partial_neighbourhood_retraction_class]: class k
      of f_i on W_i, 3.1.20, p. 232, corrected line 11. *)
  partial_neighbourhood_retraction_class : norm_class hNX hNX W f k;
  (** Source for [partial_neighbourhood_retraction_range]: values
      in B, 3.1.20, p. 232, erratum p. 4, line 11. *)
  partial_neighbourhood_retraction_range : forall x, W x -> B (f x);
  (** Source for [partial_neighbourhood_retraction_fixed]: f_i
      fixes B intersect W_i, 3.1.20, p. 232, corrected line 11. *)
  partial_neighbourhood_retraction_fixed : forall x, B x -> W x -> f x=x
}.

(** Source for [partial_neighbourhood_retraction_full]: when the
    final open domain contains B, the corrected intermediate laws
    give a retraction onto B, 3.1.20, pp. 232–233. Supporting lemma. *)
Lemma partial_neighbourhood_retraction_full (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B W:set X) (f:X->X) k :
  B `<=` W -> is_partial_neighbourhood_retraction hNX B W f k ->
  is_norm_class_retraction hNX W B f k.
Proof.
move=>hBW [hc hm hf]; constructor=>// x hx.
exact: hf hx (hBW x hx).
Qed.

(** Source for [local_retraction_partial_neighbourhood]: the local
    coordinate retractions of 3.1.19, p. 231, satisfy the corrected
    invariant for the construction in 3.1.20, p. 232. Supporting lemma. *)
Lemma local_retraction_partial_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B W:set X) (f:X->X) k :
  is_norm_class_retraction hNX W (B `&` W) f k ->
  is_partial_neighbourhood_retraction hNX B W f k.
Proof.
move=>[hc hBW hm hf]; constructor=>//.
- move=>x hx; exact (hm x hx).1.
- move=>x hx hw; exact: hf (conj hx hw).
Qed.
