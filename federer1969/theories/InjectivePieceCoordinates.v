(** Federer (1969), 3.2.18, p. 255:
    change source coordinates on a piece
    from 3.2.2. The actual map f
    composed with the inverse linear coordinate
    change has both lambda distance bounds
    and the printed differential estimates there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric RealNormUP HilbertFormCompactness
  NormMetric NormDifferentialUP NormDifferentialLinear NormDifferentialChain
  NormDifferentialLocal NormOpenDomainLaws NormFiniteLinearBound
  EuclideanLinearMaps InnerOwnNormTopology TopologicalBorel BorelFunctionBasic
  LipschitzUP MetricBiLipschitzUP PartialFunctionUP InjectiveDifferentialPieceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [injective_piece_uniform_coordinates]:
    normalize the source coordinates using s
    and s inverse from 3.2.2 in
    the combination of results proving Federer
    3.2.18, p. 255. The differential
    estimates are proved for the actual
    reparametrized map at every point of s(E). *)
Theorem injective_piece_uniform_coordinates (R : realType) m n
    (f : R_n R m -> R_n R n) (lambda : R) (E : set (R_n R m)) :
  is_injective_differential_piece f lambda E ->
  exists (s t : Hom (R_n R m) (R_n R m)),
    cancel s t /\ cancel t s /\
    @borel_set (inner_metric_space (@euclidean_inner_productP R m)) (s @` E) /\
    @is_metric_bilipschitz_bound R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R n)) (s @` E) (fun a=>f (t a)) lambda /\
    forall a, (s @` E) a -> exists D : Hom (R_n R m) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT (fun a=>f (t a)) a D /\
      forall v, lambda^-1*inner_norm (@euclidean_inner_productP R m) v<=
        inner_norm (@euclidean_inner_productP R n) (D v) /\
        inner_norm (@euclidean_inner_productP R n) (D v)<=
          lambda*inner_norm (@euclidean_inner_productP R m) v.
Proof.
move=> [hE [hLocus [hInj [s [t [g [hST [hTS [hGraph [hLip [hInv hDiff]]]]]]]]]]].
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
have hEBorel : @borel_set X E.
  exact: (inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 hE.
have hSet : (s @` E)=(t @^-1` E).
  apply/seteqP; split=> a.
  - move=> [x hx <-]; change (E (t (s x))); by rewrite hST.
  - move=> ha; exists (t a)=> //; exact: hTS.
have hTCont : continuous (fun x : X=>(t x:X)).
  exact: euclidean_linear_continuous (hom_as_linear t).
have hSBorel : @borel_set X (s @` E).
  rewrite hSet; exact: (borel_function_preimage (continuous_borel_function hTCont) hEBorel).
have hBi : @is_metric_bilipschitz_bound R X Y (s @` E) (fun a=>f (t a)) lambda.
  split; first exact hLip.
  move=> a b [x hx <-] [y hy <-].
  have hxg : partial_function_graph g (f x) x by apply: (hGraph (f x) x).2; by split.
  have hyg : partial_function_graph g (f y) y by apply: (hGraph (f y) y).2; by split.
  have hh := hInv (f x) (f y) x y hxg hyg.
  by rewrite !hST.
exists s,t; split=> //; split=> //; split=> //; split=> //.
move=> a [x hx <-].
have [L [hL _]] := hLocus x hx.
pose D := hom_comp L t.
have hTBound : norm_bounded_linear NX NX t.
  exact: (@norm_finite_linear_bounded R (R_n R m) (R_n R m) NX NX hNX hNX m
    (@coordinate_basis R m) (@coordinate_basisP R m) t).
have hT := @norm_differential_linear R (R_n R m) (R_n R m) NX NX hNX hNX
  setT (s x) t (@norm_full_domain_interior R (R_n R m) NX (s x)) hTBound.
have hL' : has_norm_differential NX NY setT f (t (s x)) L by rewrite hST.
have hChain := norm_differential_chain hNX hNX hNY hT hL'.
have hD : has_norm_differential NX NY setT (fun a=>f (t a)) (s x) D.
  apply: (norm_differential_restrict (fun _ _=>conj I I)
    (@norm_full_domain_interior R (R_n R m) NX (s x)) hChain).
exists D; split=> // v.
have hEst := ((hDiff x hx L hL).1 (t v)).
by rewrite /D hom_compE hTS in hEst *.
Qed.
