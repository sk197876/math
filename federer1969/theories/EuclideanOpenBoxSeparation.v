(** Federer (1969), 3.2.41, printed p. 277, second proof paragraph:
    two disjoint proper open boxes can be separated by a coordinate
    hyperplane. This supplies the genuine nontrivial cut used in the
    finite-family induction, without assuming its existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [disjoint_open_boxes_coordinate_separation]: supporting
    choice of i and a in Federer 3.2.41, p. 277. If every pair
    of corresponding proper intervals overlaps, their actual midpoint
    tuple is in both boxes. Consequently disjoint boxes have a pair
    of nonoverlapping coordinate intervals, including touching ends. *)
Lemma disjoint_open_boxes_coordinate_separation (R:realType) n
    (a b c d:R_n R n)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_open_coordinate_box a b A ->
  is_euclidean_open_coordinate_box c d B ->
  (forall x,A x ->B x ->False) ->
  exists i:'I_n,b i<=c i \/d i<=a i.
Proof.
move=> hA hB hDisjoint.
apply:contrapT=> hNone.
have hOverlap i:a i<d i /\c i<b i.
  split; rewrite ltNge; apply/negP=> h;
    apply:hNone; exists i; [by right|by left].
pose z:R_n R n:=[ffun i=>(Order.max (a i) (c i)+Order.min (b i) (d i))/2].
have hPoint i:a i<z i<b i /\c i<z i<d i.
  have hAB:=hA.1 i; have hCD:=hB.1 i.
  have [hAD hCB]:=hOverlap i.
  have hGap:Order.max (a i) (c i)<Order.min (b i) (d i).
    case:(leP (a i) (c i))=>[hAC|hCA].
    - have hMax:Order.max (a i) (c i)=c i:=max_r hAC.
      case:(leP (b i) (d i))=>[hBD|hDB].
      + have hMin:Order.min (b i) (d i)=b i:=min_l hBD.
        by rewrite ?hMax ?hMin.
      + have hMin:Order.min (b i) (d i)=d i:=min_r (ltW hDB).
        by rewrite ?hMax ?hMin.
    - have hMax:Order.max (a i) (c i)=a i:=max_l (ltW hCA).
      case:(leP (b i) (d i))=>[hBD|hDB].
      + have hMin:Order.min (b i) (d i)=b i:=min_l hBD.
        by rewrite ?hMax ?hMin.
      + have hMin:Order.min (b i) (d i)=d i:=min_r (ltW hDB).
        by rewrite ?hMax ?hMin.
  have hAL:a i<=Order.max (a i) (c i) by rewrite le_max lexx.
  have hCL:c i<=Order.max (a i) (c i) by rewrite le_max lexx orbT.
  have hUB:Order.min (b i) (d i)<=b i by rewrite ge_min lexx.
  have hUD:Order.min (b i) (d i)<=d i by rewrite ge_min lexx orbT.
  rewrite /z ffunE.
  have hDouble:(Order.max (a i) (c i)+Order.min (b i) (d i))/2+
      (Order.max (a i) (c i)+Order.min (b i) (d i))/2=
      Order.max (a i) (c i)+Order.min (b i) (d i) by field.
  split; apply/andP; split; lra.
apply:(hDisjoint z).
- apply:(hA.2 z).2=> i; exact:(hPoint i).1.
- apply:(hB.2 z).2=> i; exact:(hPoint i).2.
Qed.

(** Source for [disjoint_open_boxes_strict_cut]: supporting actual
    separating coordinate hyperplane of Federer 3.2.41, p. 277.
    Each original box lies wholly in one strict halfspace, so each
    side of a finite-family split omits an entire original member. *)
Lemma disjoint_open_boxes_strict_cut (R:realType) n (a b c d:R_n R n)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_open_coordinate_box a b A ->
  is_euclidean_open_coordinate_box c d B ->
  (forall x,A x ->B x ->False) ->
  exists (i:'I_n) (t:R),
    ((forall x,A x ->x i<t) /\(forall x,B x ->t<x i)) \/
    ((forall x,B x ->x i<t) /\(forall x,A x ->t<x i)).
Proof.
move=> hA hB hDisjoint.
have [i [hBC|hDA]]:=disjoint_open_boxes_coordinate_separation hA hB hDisjoint.
- exists i,(b i); left; split=> x hx.
  + have /andP[_ h]:=(hA.2 x).1 hx i; exact h.
  + have /andP[hcx _]:=(hB.2 x).1 hx i; exact:le_lt_trans hBC hcx.
- exists i,(d i); right; split=> x hx.
  + have /andP[_ h]:=(hB.2 x).1 hx i; exact h.
  + have /andP[hax _]:=(hA.2 x).1 hx i; exact:le_lt_trans hDA hax.
Qed.
