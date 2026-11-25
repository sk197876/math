(** Federer (1969), 4.1.8, p. 360: uniqueness
    follows from 4.1.3, p. 348, and continuity.
    This supporting topological rule uses only inverse images
    of open sets and the ordinary real scalar topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormOpenTopology OpenFamilyTopologyUP DirectedSeminormFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_image_scalar_zero]: a continuous real
    function vanishing on a dense image vanishes everywhere,
    supporting the uniqueness in Federer 4.1.8, p. 360.
    No metric or vector topology on the source is required. *)
Theorem dense_image_scalar_zero (R:realType) (X W:Type) (O:set (set X))
    (F:W->X) (L:X->R^o):
  (forall x V,O V->V x->exists w,V (F w))->
  open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R)) L->
  (forall w,L (F w)=0)->forall x,L x=0.
Proof.
move=>hDense hContinuous hZero x.
apply:contrapT=>hNonzero.
have hOpen:norm_open_family (@scalar_absolute_value_norm R) [set t:R^o|t<>0].
  apply:((@norm_open_family_seminorm_laws R R^o (fun t=>`|t|)
    (@scalar_absolute_value_norm R)).2 _).2=>t ht.
  exists tt,`|t|;split;first by rewrite normr_gt0;apply/eqP.
  move=>y hy hYzero;subst y.
  by rewrite sub0r normrN ltxx in hy.
have hV:=hContinuous [set t:R^o|t<>0] hOpen.
have[w hw]:=hDense x [set y|L y<>0] hV hNonzero.
apply:hw;exact:hZero.
Qed.
