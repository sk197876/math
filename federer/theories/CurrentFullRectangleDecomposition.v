(** Federer (1969), 4.1.11, p. 366: repeated
    use of the original prism formula decomposes the
    original m-fold oriented segment product into exactly
    m! oriented m-simplexes. Retain every original corner,
    arbitrary factor dimensions and degenerate endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Biorthogonal
  CurrentSpaces CurrentDirac OrientedSegmentFactor OrientedRectangleDomain CurrentFullRectangleDomain
  CurrentFullRectangle CurrentFullRectangleVertex EuclideanFundamentalCurrentPoint
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexCurrentLowDegrees OrientedSimplexSignedVertex CurrentCartesianPointInclusion
  CurrentAmbientCartesianProduct CurrentAmbientProductFiniteSums CurrentPrismVerticesSealed
  CurrentPrismVertexProperty CurrentSimplexPrism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentFullRectangleDecomposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).
Local Notation D := (@oriented_rectangle_dimension R).
Local Notation F := (fun n m (v:'I_(m.+1)->R_n R n)=>@OrientedSimplexCurrent.value R h2 n m v).

(** Source for [current_full_rectangle_decomposition]: the original
    finite m-fold segment product is a sum of exactly
    m! oriented m-simplexes with original corner vertices,
    Federer 4.1.11, p. 366. The factors may have
    arbitrary Euclidean dimensions; the current degree is
    their number. Empty families and repeated endpoints remain included. *)
Theorem current_full_rectangle_decomposition (f:seq Factor):
  forall hf:is_current_full_rectangle_family f,
  exists I:finType,exists v:I->'I_((size f).+1)->R_n R (D f),
    #|I|=((size f)`!)%N /\
    @current_full_rectangle R h2 f hf=\sum_(k:I) F (D f) (size f) (v k) /\
    forall k l,@is_current_full_rectangle_vertex R f (v k l).
Proof.
elim:f=>[|a [|b t] ih] hf.
- exists (Finite.clone 'I_1 _);exists (fun _ _=>0);split;first by rewrite card_ord.
  split.
  + rewrite current_full_rectangle_empty euclidean_fundamental_current_point.
    by rewrite big_ord_recl big_ord0 addr0 oriented_simplex_current_point.
  + move=>k l;exact:current_full_rectangle_empty_vertex.
- pose w:'I_2->R_n R (oriented_segment_factor_dimension a):=
    ordinal_cons (oriented_segment_factor_start a) (fun _:'I_1=>oriented_segment_factor_end a).
  exists (Finite.clone 'I_1 _);exists (fun _=>w);split;first by rewrite card_ord.
  split.
  + rewrite current_full_rectangle_single big_ord_recl big_ord0 addr0.
    have hSegment:=@oriented_simplex_current_segment R h2 (oriented_segment_factor_dimension a) w
      (fun (s:R) (_:s \in `[0,1])=>Logic.I).
    by rewrite /w ordinal_cons0 ordinal_consS in hSegment;rewrite -hSegment.
  + move=>k l;apply/current_full_rectangle_single_vertex.
    case:(unliftP ord0 l)=>[r ->|->].
    * right;by rewrite /w ordinal_consS.
    * left;by rewrite /w ordinal_cons0.
- have[I [v [hCard [hRectangle hCorners]]]]:=ih hf.2.
  pose J:finType:=Finite.clone (I*'I_((size (b::t)).+1))%type _.
  pose Lower:=@current_cartesian_point_inclusion R (oriented_segment_factor_dimension a) (D (b::t))
    (oriented_segment_factor_start a).
  pose Upper:=@current_cartesian_point_inclusion R (oriented_segment_factor_dimension a) (D (b::t))
    (oriented_segment_factor_end a).
  pose P (k:J):'I_((size (b::t)).+2)->R_n R (D (a::b::t)):=
    @CurrentPrismVertices.value (R_n R (D (b::t))) (R_n R (D (a::b::t)))
      Lower Upper (size (b::t)) (v k.1) k.2.
  have hSigned (k:J):exists w:'I_((size (b::t)).+2)->R_n R (D (a::b::t)),
      F (D (a::b::t)) (size (a::b::t)) w=
        (-1:R)^+(val k.2)*:F (D (a::b::t)) (size (a::b::t)) (P k) /\
      forall l,exists r,w l= P k r.
    exact:(@oriented_simplex_signed_vertices R h2 (D (a::b::t)) (size (b::t)) (P k) (val k.2)).
  pose w (k:J):=projT1 (cid (hSigned k)).
  have hValues (k:J):F (D (a::b::t)) (size (a::b::t)) (w k)=
      (-1:R)^+(val k.2)*:F (D (a::b::t)) (size (a::b::t)) (P k):=
    (projT2 (cid (hSigned k))).1.
  have hVertices (k:J) l:exists r,w k l= P k r:=(projT2 (cid (hSigned k))).2 l.
  exists J;exists w;split.
  + rewrite /J card_prod card_ord hCard /= factS.
    exact:mulnC.
  + split.
    * rewrite current_full_rectangle_attach hRectangle.
      have hConstant (X:finType) (T:X->@current_space R h2 (D (b::t))
          (fun _=>True)
          (fun x (_:True)=>@norm_full_domain_interior R (R_n R (D (b::t)))
            (inner_norm (@euclidean_inner_productP R (D (b::t)))) x) (size (b::t))):
          \sum_(k:X) T k=\sum_(k:X) (1:R)*:T k.
        apply:eq_bigr=>k _;by rewrite scale1r.
      rewrite (hConstant I (fun k=>F (D (b::t)) (size (b::t)) (v k)))
        current_ambient_product_second_weighted_sum.
      transitivity (\sum_(r:I) \sum_(s<(size (b::t)).+1)
        (-1:R)^+s*:F (D (a::b::t)) (size (a::b::t)) (P (r,s))).
      -- apply:eq_bigr=>r _;rewrite scale1r.
         exact:(@current_simplex_prism_formula R h2 (size (b::t))
           (oriented_segment_factor_dimension a) (D (b::t))
           (oriented_segment_factor_start a) (oriented_segment_factor_end a) (v r)).
      -- rewrite pair_bigA;apply:eq_bigr=>k _;exact:esym (hValues k).
    * move=>k l;have[r ->]:=hVertices k l.
      apply:(@current_prism_vertex_property (R_n R (D (b::t)))
        (R_n R (D (a::b::t))) Lower Upper (size (b::t)) (v k.1) k.2
        (@is_current_full_rectangle_vertex R (a::b::t))).
      -- move=>s;apply:current_full_rectangle_vertex_join;first by left.
         exact:hCorners.
      -- move=>s;apply:current_full_rectangle_vertex_join;first by right.
         exact:hCorners.
Qed.
End CurrentFullRectangleDecomposition.
