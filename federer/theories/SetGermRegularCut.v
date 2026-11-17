(** Federer (1969), 3.4.8(11), p. 334:
    the complement of the enlarged ideal variety
    is the original regular Z cut by chi!=0.
    The old exceptional variety is already contained
    in the new one. The exact product chi*Delta
    uses the original nonvanishing of Delta on Z. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermExistence SetGermLaws SetGermOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [set_germ_regular_product_cut]:
    the original equality of the final regular
    part and gamma_0(D), 3.4.8(11), p. 334.
    The assumptions are exact preceding variety and
    equation identities, not a component or dimension
    conclusion. *)
Theorem set_germ_regular_product_cut (X:topologicalType) (R:fieldType) a
    (alpha eta gamma:@set_germ_space X a) (Z:set X) (chi delta:X->R):
  alpha = @SetGerms.join X a eta (@set_germ X a Z) ->
  set_germ_subset eta gamma ->
  gamma = @SetGerms.meet X a alpha (@set_germ X a [set x|chi x*delta x=0]) ->
  (forall x,Z x ->delta x<>0) ->
  @SetGerms.meet X a alpha (@SetGerms.neg X a gamma) =
    @set_germ X a [set x|Z x /\chi x<>0].
Proof.
have [A <-]:=@set_germ_has_representative X a alpha.
have [E <-]:=@set_germ_has_representative X a eta.
have [G <-]:=@set_germ_has_representative X a gamma.
move=>hUnion hContained hCut hDelta.
rewrite (@set_germ_union_equation X a _ _ _ (@SetGerms.laws X a)) in hUnion.
have [U [hU [haU hAUnion]]]:=(@set_germ_equality_original X a A (E `|` Z)).1 hUnion.
have [V [hV [haV hEG]]]:=(@set_germ_subset_original X a E G).1 hContained.
rewrite (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)) in hCut.
have [W [hW [haW hGCut]]]:=(@set_germ_equality_original X a G
  (A `&` [set x|chi x*delta x=0])).1 hCut.
rewrite (@set_germ_complement_equation X a _ _ _ (@SetGerms.laws X a))
  (@set_germ_intersection_equation X a _ _ _ (@SetGerms.laws X a)).
apply/set_germ_equality_original;exists (U `&` (V `&` W));split;first exact:openI hU (openI hV hW).
split;first by split;last split.
apply/seteqP;split.
- move=>x [[hAx hNotG] hLocal];split;last exact:hLocal.
  have hMembership:((E `|` Z) `&` U) x by rewrite -hAUnion;split;[exact:hAx|exact:hLocal.1].
  have hZx:Z x.
    case:hMembership.1=>hEx;last exact:hEx.
    exfalso;apply:hNotG;exact:hEG x hEx hLocal.2.1.
  split;first exact:hZx.
  move=>hZero;apply:hNotG.
  have hRight:((A `&` [set x|chi x*delta x=0]) `&` W) x.
    split;last exact:hLocal.2.2.
    split;first exact:hAx.
    by change (chi x*delta x = 0);rewrite hZero mul0r.
  rewrite -hGCut in hRight;exact:hRight.1.
- move=>x [[hZx hNotChi] hLocal];split;last exact:hLocal.
  have hMembership:(A `&` U) x.
    rewrite hAUnion;split;[by right|exact:hLocal.1].
  split;first exact:hMembership.1.
  move=>hGx.
  have hRight:((A `&` [set x|chi x*delta x=0]) `&` W) x by rewrite -hGCut;split;[exact:hGx|exact:hLocal.2.2].
  have hZero:chi x*delta x=0:=hRight.1.2.
  move/eqP:hZero;rewrite mulf_eq0=>/orP [/eqP h|/eqP h].
  + exact:hNotChi h.
  + exact:hDelta x hZx h.
Qed.
