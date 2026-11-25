(** Federer (1969), 4.1.11, p. 366: repeated
    application of the original prism formula represents
    an m-dimensional oriented rectangle by m! oriented
    m-simplexes, with all vertices among the original
    rectangle vertices. The proof uses only the preceding
    opaque rectangle and simplex laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates Biorthogonal EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentDirac
  OrientedRectangleDomain ScalarSegmentFactors CurrentScalarRectangle CurrentScalarRectangleVertex
  EuclideanFundamentalCurrentPoint OrientedSimplexCurrentUP OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexCurrentLowDegrees OrientedSimplexSignedVertex
  CurrentCartesianPointInclusion CurrentAmbientCartesianProduct CurrentAmbientProductFiniteSums
  CurrentPrismVerticesSealed CurrentPrismVertexProperty CurrentSimplexPrism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentScalarRectangleDecomposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation D := (fun f=>oriented_rectangle_dimension (@scalar_segment_factors R f)).
Local Notation F := (fun n m (v:'I_(m.+1)->R_n R n)=>@OrientedSimplexCurrent.value R h2 n m v).

(** Source for [current_scalar_rectangle_decomposition]: the
    original rectangular decomposition has exactly m!
    oriented m-simplexes; every ordered vertex remains
    an original rectangle vertex, Federer 4.1.11,
    p. 366. No ordering or nondegeneracy is imposed
    on the endpoint pairs, and m=0 is included. *)
Theorem current_scalar_rectangle_decomposition (f:seq (R*R)):
  exists I:finType,exists v:I->'I_((D f).+1)->R_n R (D f),
    #|I|=((size f)`!)%N /\
    @current_scalar_rectangle R h2 f=\sum_(k:I) F (D f) (D f) (v k) /\
    forall k l,@is_current_scalar_rectangle_vertex R f (v k l).
Proof.
elim:f=>[|a [|b t] ih].
- exists (Finite.clone 'I_1 _);exists (fun _ _=>0);split;first by rewrite card_ord.
  split.
  + rewrite current_scalar_rectangle_empty euclidean_fundamental_current_point.
    by rewrite big_ord_recl big_ord0 addr0 oriented_simplex_current_point.
  + move=>k l;exact:current_scalar_rectangle_empty_vertex.
- pose w:'I_2->R_n R 1%N:=ordinal_cons (@euclidean_one_embed R a.1)
    (fun _:'I_1=>@euclidean_one_embed R a.2).
  exists (Finite.clone 'I_1 _);exists (fun _=>w);split;first by rewrite card_ord.
  split.
  + rewrite current_scalar_rectangle_single big_ord_recl big_ord0 addr0.
    have hSegment:=@oriented_simplex_current_segment R h2 1%N w
      (fun (s:R) (_:s \in `[0,1])=>Logic.I).
    by rewrite /w ordinal_cons0 ordinal_consS in hSegment;rewrite -hSegment.
  + move=>k l;apply/current_scalar_rectangle_single_vertex.
    case:(unliftP ord0 l)=>[r ->|->].
    * right;by rewrite /w ordinal_consS /euclidean_one_embed ffunE.
    * left;by rewrite /w ordinal_cons0 /euclidean_one_embed ffunE.
- move:ih=>[I [v [hCard [hRectangle hCorners]]]].
  pose J:finType:=Finite.clone (I*'I_((D (b::t)).+1))%type _.
  pose Lower:=@current_cartesian_point_inclusion R 1%N (D (b::t)) (@euclidean_one_embed R a.1).
  pose Upper:=@current_cartesian_point_inclusion R 1%N (D (b::t)) (@euclidean_one_embed R a.2).
  pose P (k:J):'I_((D (b::t)).+2)->R_n R (D (a::b::t)):=
    @CurrentPrismVertices.value (R_n R (D (b::t))) (R_n R (D (a::b::t)))
      Lower Upper (D (b::t)) (v k.1) k.2.
  have hSigned (k:J):exists w:'I_((D (b::t)).+2)->R_n R (D (a::b::t)),
      F (D (a::b::t)) (D (a::b::t)) w=
        (-1:R)^+(val k.2)*:F (D (a::b::t)) (D (a::b::t)) (P k) /\
      forall l,exists r,w l= P k r.
    exact:(@oriented_simplex_signed_vertices R h2 (D (a::b::t)) (D (b::t)) (P k) (val k.2)).
  pose w (k:J):=projT1 (cid (hSigned k)).
  have hValues (k:J):F (D (a::b::t)) (D (a::b::t)) (w k)=
      (-1:R)^+(val k.2)*:F (D (a::b::t)) (D (a::b::t)) (P k):=
    (projT2 (cid (hSigned k))).1.
  have hVertices (k:J) l:exists r,w k l= P k r:=(projT2 (cid (hSigned k))).2 l.
  exists J;exists w;split.
  + rewrite /J card_prod card_ord hCard factS.
    rewrite scalar_rectangle_dimension.
    exact:mulnC.
  + split.
    * rewrite current_scalar_rectangle_attach hRectangle.
      pose S:=@current_scalar_rectangle R h2 [::a].
      have hConstant (X:finType) (T:X->@current_space R h2 (D (b::t))
          (fun _=>True)
          (fun x (_:True)=>@norm_full_domain_interior R (R_n R (D (b::t)))
            (inner_norm (@euclidean_inner_productP R (D (b::t)))) x) (D (b::t))):
          \sum_(k:X) T k=\sum_(k:X) (1:R)*:T k.
        apply:eq_bigr=>k _;by rewrite scale1r.
      rewrite (hConstant I (fun k=>F (D (b::t)) (D (b::t)) (v k)))
        current_ambient_product_second_weighted_sum.
      transitivity (\sum_(r:I) \sum_(s<(D (b::t)).+1)
        (-1:R)^+s*:F (D (a::b::t)) (D (a::b::t)) (P (r,s))).
      -- apply:eq_bigr=>r _;rewrite scale1r.
         exact:(@current_simplex_prism_formula R h2 (D (b::t)) 1%N (D (b::t))
           (@euclidean_one_embed R a.1) (@euclidean_one_embed R a.2) (v r)).
      -- rewrite pair_bigA;apply:eq_bigr=>k _;exact:esym (hValues k).
    * move=>k l;have[r ->]:=hVertices k l.
      apply:(@current_prism_vertex_property (R_n R (D (b::t)))
        (R_n R (D (a::b::t))) Lower Upper (D (b::t)) (v k.1) k.2
        (@is_current_scalar_rectangle_vertex R (a::b::t))).
      -- move=>s;apply:current_scalar_rectangle_vertex_join;first by left.
         exact:hCorners.
      -- move=>s;apply:current_scalar_rectangle_vertex_join;first by right.
         exact:hCorners.
Qed.
End CurrentScalarRectangleDecomposition.
