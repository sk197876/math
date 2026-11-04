(** Federer (1969), 3.2.47, p. 283: supporting
    differentiability classes of actual Cartesian product charts.
    The two coordinate projections and inclusions are the
    original orthogonal block maps of 2.6.5, p. 120.
    All classes follow from the proved linear composition
    and addition laws of 3.1.11, pp. 219–220. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  NormClassOneUP NormRegularity NormRegularityOperations NormRegularityLinearMaps
  NormFiniteLinearBound EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_intersection_domain_interior]: finite
    intersections of actual open chart domains stay open,
    supporting the product chart in 3.2.47, p. 283,
    by the interior convention of 3.1.1, p. 209. *)
Lemma norm_intersection_domain_interior (R:realType) (X:lmodType R)
    (NX:X->R) (A B:set X) x:
  norm_domain_interior NX A x ->norm_domain_interior NX B x ->
  norm_domain_interior NX (A `&` B) x.
Proof.
move=>[r [hr hA]] [s [hs hB]].
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=>v; rewrite lt_min=>/andP [hvr hvs]; split; [exact:hA v hvr|exact:hB v hvs].
Qed.

(** Source for [norm_class_euclidean_block_pair]: assembling
    two class-k maps by the actual orthogonal block join
    preserves class k, supporting 3.2.47, p. 283. *)
Theorem norm_class_euclidean_block_pair (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n v (A:set X)
    (f:X->R_n R n) (g:X->R_n R v) k:
  norm_class hNX (inner_norm_real_norm (@euclidean_inner_productP R n)) A f k ->
  norm_class hNX (inner_norm_real_norm (@euclidean_inner_productP R v)) A g k ->
  norm_class hNX (inner_norm_real_norm (@euclidean_inner_productP R (n+v))) A
    (fun x=>euclidean_block_join (f x,g x)) k.
Proof.
move=>hf hg.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hV:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose hP:=inner_norm_real_norm (@euclidean_inner_productP R (n+v)).
pose i:=@euclidean_first_injection_map R n v.
pose j:=@euclidean_last_injection_map R n v.
have hI:=@norm_finite_linear_bounded R (R_n R n) (R_n R (n+v)) _ _ hN hP
  n (@coordinate_basis R n) (@coordinate_basisP R n) i.
have hJ:=@norm_finite_linear_bounded R (R_n R v) (R_n R (n+v)) _ _ hV hP
  v (@coordinate_basis R v) (@coordinate_basisP R v) j.
have hLeft:=@norm_class_postcompose_linear R X (R_n R n) (R_n R (n+v))
  NX _ _ hNX hN hP A f i k hI hf.
have hRight:=@norm_class_postcompose_linear R X (R_n R v) (R_n R (n+v))
  NX _ _ hNX hV hP A g j k hJ hg.
have hSum:=@norm_class_add R X (R_n R (n+v)) NX _ hNX hP A
  (fun x=>i (f x)) (fun x=>j (g x)) k hLeft hRight.
have hFormula:(fun x=>euclidean_block_join (f x,g x))=(fun x=>i (f x)+j (g x)).
  apply:funext=>x; exact:euclidean_block_join_sum.
by rewrite -hFormula in hSum.
Qed.

(** Source for [euclidean_cartesian_norm_class]: products of
    actual class-k chart maps are class k on their
    original product domains, supporting the local product proof
    of 3.2.47, p. 283. Empty coordinate blocks remain. *)
Theorem euclidean_cartesian_norm_class (R:realType) m mu n v
    (A:set (R_n R m)) (B:set (R_n R mu))
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R v) k:
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R mu))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) B g k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (m+mu)))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+v)))
    (euclidean_cartesian_set A B) (euclidean_cartesian_map f g) k.
Proof.
move=>hf hg.
pose X:=R_n R (m+mu).
pose hX:=inner_norm_real_norm (@euclidean_inner_productP R (m+mu)).
pose hM:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hMu:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hV:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose P:=@euclidean_first_block_map R m mu.
pose Q:=@euclidean_last_block_map R m mu.
have hP:=@norm_finite_linear_bounded R X (R_n R m) _ _ hX hM
  (m+mu)%N (@coordinate_basis R (m+mu)) (@coordinate_basisP R (m+mu)) P.
have hQ:=@norm_finite_linear_bounded R X (R_n R mu) _ _ hX hMu
  (m+mu)%N (@coordinate_basis R (m+mu)) (@coordinate_basisP R (m+mu)) Q.
have hLeft:=@norm_class_precompose_linear R X (R_n R m) (R_n R n) _ _ _ hX hM hN A f P k hP hf.
have hRight:=@norm_class_precompose_linear R X (R_n R mu) (R_n R v) _ _ _ hX hMu hV B g Q k hQ hg.
pose D:=euclidean_cartesian_set A B.
have hOpen x (hx:D x):norm_domain_interior (inner_norm (@euclidean_inner_productP R (m+mu))) D x.
  exact (@norm_intersection_domain_interior R X _ (fun x=>A (P x)) (fun x=>B (Q x)) x
    ((@norm_class_continuous R X (R_n R n) _ _ hX hN _ _ k hLeft x hx.1).1)
    ((@norm_class_continuous R X (R_n R v) _ _ hX hV _ _ k hRight x hx.2).1)).
have hLeftD:=@norm_class_open_restriction R X (R_n R n) _ _ hX hN
  (fun x=>A (P x)) D (fun x=>f (P x)) k (fun x hx=>hx.1) hOpen hLeft.
have hRightD:=@norm_class_open_restriction R X (R_n R v) _ _ hX hV
  (fun x=>B (Q x)) D (fun x=>g (Q x)) k (fun x hx=>hx.2) hOpen hRight.
exact (@norm_class_euclidean_block_pair R X _ hX n v D (fun x=>f (P x)) (fun x=>g (Q x))
  k hLeftD hRightD).
Qed.
