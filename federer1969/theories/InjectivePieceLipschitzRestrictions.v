(** Federer (1969), 3.2.9, p. 247: the
    pieces from 3.2.2 have Lipschitz forward and
    inverse restrictions. Convert the printed transformed
    bounds through finite bounds of the source
    automorphism and its inverse. The inverse total
    representative uses only the existing opaque extension. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP NormDifferentialUP NormFiniteLinearBound InjectiveDifferentialPieceUP
  LipschitzUP LipschitzBasic PartialFunctionUP PartialFunctionExtensionUP PartialFunctionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [injective_piece_forward_inverse_lipschitz]:
    the application of 3.2.2 in the proof
    of Federer 3.2.9, p. 247. Its
    source automorphism and inverse have finite norm
    bounds, giving ordinary Lipschitz restrictions and
    a total inverse representative agreeing on the
    exact image. No inverse is assigned outside
    the image by the mathematical conclusion. *)
Theorem injective_piece_forward_inverse_lipschitz (R:realType) m n
    (f:R_n R m->R_n R n) (lambda:R) (E:set (R_n R m)):
  is_injective_differential_piece f lambda E ->
  @is_metric_lipschitz R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] E f /\
  exists g:R_n R n->R_n R m,
    @is_metric_lipschitz R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] (f @` E) g /\
    forall x,E x -> g (f x)=x.
Proof.
move=>hPiece.
pose X:=R_n R m; pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
have hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
have [s [t [g [hST [hTS [hg [hForward [hInverse hModel]]]]]]]]:=hPiece.2.2.2.
have [Cs [hCs hSB]]:=norm_finite_linear_bounded hNX hNX (@coordinate_basisP R m) s.
have [Ct [hCt hTB]]:=norm_finite_linear_bounded hNX hNX (@coordinate_basisP R m) t.
have hLambda:0<=lambda:=hForward.1.
split.
- apply:(@metric_lipschitz_of_bound R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] E f (lambda*Cs)).
  split; first exact:mulr_ge0 hLambda hCs.
  move=>x y hx hy.
  have hsx:(s @` E) (s x) by exists x.
  have hsy:(s @` E) (s y) by exists y.
  have hh:=hForward.2 (s x) (s y) hsx hsy.
  change (is_true (NY (f (t (s x))-f (t (s y)))<=lambda*NX (s x-s y))) in hh.
  rewrite !hST in hh.
  have hS:=hSB (x-y); rewrite linearB in hS.
  change (is_true (NY (f x-f y)<=(lambda*Cs)*NX (x-y))).
  rewrite -mulrA; exact (le_trans hh (ler_wpM2l hLambda hS)).
- pose G:=@PartialFunctionExtension.value Y X g 0.
  have hG:is_partial_function_total_extension g G:=@PartialFunctionExtension.laws Y X g 0.
  have hAgreement x:E x -> G (f x)=x.
    move=>hx; apply:(hG (f x) x); exact ((hg (f x) x).2 (conj hx (erefl _))).
  exists G; split; last exact hAgreement.
  apply:(@metric_lipschitz_of_bound R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] (f @` E) G (Ct*lambda)).
  split; first exact:mulr_ge0 hCt hLambda.
  move=>y z [x hx <-] [w hw <-].
  rewrite !hAgreement //.
  have hGx:partial_function_graph g (f x) x:=(hg (f x) x).2 (conj hx (erefl _)).
  have hGw:partial_function_graph g (f w) w:=(hg (f w) w).2 (conj hw (erefl _)).
  have hInv:=hInverse (f x) (f w) x w hGx hGw.
  have hT:=hTB (s x-s w).
  have hEq:t (s x-s w)=x-w by rewrite -linearB hST.
  rewrite hEq in hT.
  change (is_true (NX (x-w)<=(Ct*lambda)*NY (f x-f w))).
  rewrite -mulrA; exact (le_trans hT (ler_wpM2l hCt hInv)).
Qed.
