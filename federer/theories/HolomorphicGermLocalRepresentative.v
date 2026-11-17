(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), pp. 327, 333:
    the actual union of S0 and earlier strata
    is holomorphic on a sufficiently small neighbourhood
    when its germ is a holomorphic variety germ.
    This is the previously proved germ/open-cover
    equivalence, restricted to the original centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric SetGermUP HolomorphicVarietyGermUP HolomorphicSetLocalCover
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_local_representative]:
    choose the original holomorphic starting set for
    the next irreducible component in the ordered
    reduction of 3.4.12, p. 339, extending 3.4.8(11), p. 333.
    The actual representative is retained on the
    chosen neighbourhood; no strata are restricted. *)
Theorem holomorphic_germ_local_representative (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U S:set X):
  U 0 ->@open (real_norm_metric_space hNX) U ->
  @is_holomorphic_variety_germ R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S) ->
  exists W:set X,W 0 /\W `<=` U /\
    @is_finite_holomorphic_variety R X NX hNX W (W `&` S).
Proof.
move=>hU0 hU hVariety.
have hLocal:@is_holomorphic_set_in R X NX hNX [set 0] S.
  by move=>a ->.
have hCover:=(@holomorphic_set_local_cover_equivalence R X NX hNX [set 0] S).1 hLocal.
have [V [hV0 hV]]:=hCover 0 (erefl _).
pose W:set X:=U `&` V.
have hW:@open (real_norm_metric_space hNX) W:=openI hU hV.1.
exists W;split;first by split.
split;first by move=>x hx;exact:hx.1.
have hRestriction:=@finite_holomorphic_variety_open_restriction R X NX hNX V W (V `&` S) hV hW
  (fun x hx=>hx.2).
have hSame:W `&` (V `&` S) = W `&` S.
  apply/seteqP;split.
  - by move=>x [hx [_ hSx]];split.
  - move=>x [hx hSx];split;first exact:hx.
    split;[exact:hx.2|exact:hSx].
by rewrite hSame in hRestriction.
Qed.
