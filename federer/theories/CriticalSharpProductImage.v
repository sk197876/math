(** Federer (1969), 3.4.4, p. 318: the
    exact image of the original coordinatewise critical source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanOneCoordinate RealMetricBackground CriticalSharpProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_sharp_product_exact_image]: the
    printed equality f(B)=R^m intersect {y:y_i in A(beta,n)
    for i>nu}, 3.4.4, p. 318. Actual
    finite-coordinate choices give preimages, while the forward
    coordinate laws prove containment. No image equality or
    measurability conclusion is added as a premise. *)
Theorem critical_sharp_product_exact_image (R:realType) m nu g
    (F:R_n R m->R_n R m) (A B:set (real_line_metric R)):
  is_critical_sharp_product_map nu g F ->
  (fun t:real_line_metric R=>g (euclidean_one_embed t)) @` A=B ->
  F @` (@critical_sharp_product_source R m nu A)=
    @critical_sharp_product_source R m nu B.
Proof.
move=>hF hImage.
apply/seteqP;split=>y.
- move=>[x hx <-] i hi.
  have hIndex:~~(i<nu)%N by rewrite -leqNgt.
  rewrite hF (negPf hIndex) -hImage.
  exists (x i);first exact:hx i hi.
  reflexivity.
- move=>hy.
  have hEach (i:'I_m):exists t:real_line_metric R,
      if (i<nu)%N then t=y i else A t /\g (euclidean_one_embed t)=y i.
    case hIndex:(i<nu)%N.
    + by exists (y i).
    + have hi:(nu<=i)%N by rewrite leqNgt hIndex.
      have hB:=hy i hi.
      rewrite -hImage in hB.
      have [t ht hValue]:=hB.
      exists t;by split.
  have [x hX]:=choice hEach.
  exists [ffun i=>x i].
  + move=>i hi;rewrite ffunE.
    have hIndex:~~(i<nu)%N by rewrite -leqNgt.
    have h:=hX i;rewrite (negPf hIndex) in h;exact:h.1.
  + apply/ffunP=>i;rewrite hF ffunE.
    have h:=hX i.
    by case hIndex:(i<nu)%N;rewrite hIndex in h;[exact:h|exact:h.2].
Qed.
