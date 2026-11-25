(** Federer (1969), 4.1.11, p. 366: an
    affine image of the original rectangular decomposition
    retains its factorial count and original corner images.
    In particular the statement applies in every Euclidean
    ambient space, without assuming target nondegeneracy. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  CurrentSpaces OrientedRectangleDomain ScalarSegmentFactors CurrentScalarRectangle
  CurrentScalarRectangleVertex CurrentScalarRectangleDecomposition CurrentCompactFiniteFamily
  CurrentCompactPushforwardAlgebra CurrentCompactMapFiniteSum CurrentCartesianMapPullback
  CurrentJoinAffineSourcePushforward OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentAffineRectangleDecomposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation D := (fun f=>oriented_rectangle_dimension (@scalar_segment_factors R f)).
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation Compact := (fun n k (T:@current_space R h2 n (Full n) (hFull n) k)=>
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n (Full n) (hFull n) k T)).

(** Source for [current_scalar_rectangle_compact]: the
    original rectangle has compact support, supporting its
    affine simplex decomposition in Federer 4.1.11,
    p. 366. Reuse the already proved finite decomposition. *)
Lemma current_scalar_rectangle_compact f:
  Compact (D f) (D f) (@current_scalar_rectangle R h2 f).
Proof.
have[I [v [hCard [hSum hVertices]]]]:=@current_scalar_rectangle_decomposition R h2 f.
rewrite hSum.
apply:(@current_compact_finite_family R h2 (D f) (Full (D f)) (hFull (D f)) (D f) I).
move=>k;exact:oriented_simplex_current_compact.
Qed.

(** Source for [current_affine_rectangle_decomposition]: any
    affine image of an original m-dimensional oriented
    rectangle is the sum of m! oriented m-simplexes
    with vertices among its original corner images,
    Federer 4.1.11, p. 366. Singular maps, repeated
    endpoints and dimension zero remain allowed. *)
Theorem current_affine_rectangle_decomposition f n
    (A:R_n R (D f)->R_n R n) (hA:is_affine_map A)
    (hRectangle:Compact (D f) (D f) (@current_scalar_rectangle R h2 f)):
  exists I:finType,exists w:I->'I_((D f).+1)->R_n R n,
    #|I|=((size f)`!)%N /\
    @current_join_affine_current R h2 (D f) n A hA (D f)
      (@current_scalar_rectangle R h2 f) hRectangle=
      \sum_(k:I) @OrientedSimplexCurrent.value R h2 n (D f) (w k) /\
    forall k l,exists x:R_n R (D f),
      @is_current_scalar_rectangle_vertex R f x /\ w k l=A x.
Proof.
have[I [v [hCard [hSum hVertices]]]]:=@current_scalar_rectangle_decomposition R h2 f.
pose S:=fun k:I=>@OrientedSimplexCurrent.value R h2 (D f) (D f) (v k).
pose hS:=fun k=>@oriented_simplex_current_compact R h2 (D f) (D f) (v k).
pose a:=fun _:I=>(1:R).
pose Sum:=\sum_(k:I) a k*:S k.
pose hSumCompact:=@current_compact_weighted_finite_family R h2 (D f)
  (Full (D f)) (hFull (D f)) (D f) I a S hS.
have hInputEquality:(@current_scalar_rectangle R h2 f)=Sum.
  rewrite hSum /Sum;apply:eq_bigr=>k _;by rewrite /a scale1r.
pose AGlobal:=@euclidean_affine_map_smooth R (D f) n (Full (D f)) (hFull (D f)) A hA.
pose AClass:=@current_cartesian_factor_open_class R (D f) n
  (Full (D f)) (hFull (D f)) A AGlobal.
pose Image:=fun (x:R_n R (D f)) (_:True)=>Logic.I.
have hInput:=@current_compact_map_pushforward_congruence R h2 (D f) n
  (Full (D f)) (Full n) (hFull (D f)) (hFull n) A Image AClass (D f)
  (@current_scalar_rectangle R h2 f) Sum hRectangle hSumCompact hInputEquality.
have hImages:=@current_compact_map_weighted_family R h2 (D f) n
  (Full (D f)) (Full n) (hFull (D f)) (hFull n) (D f)
  A Image AClass I a S hS hSumCompact.
exists I;exists (fun k l=>A (v k l));split;first exact:hCard.
split.
- rewrite /current_join_affine_current hInput hImages.
  apply:eq_bigr=>k _;rewrite /a scale1r.
  exact:(@oriented_simplex_current_affine R h2 (D f) n A hA (D f) (v k) (hS k)).
- move=>k l;exists (v k l);split;first exact:hVertices.
  by [].
Qed.
End CurrentAffineRectangleDecomposition.
