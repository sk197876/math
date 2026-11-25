(** Federer (1969), 4.1.27, p. 384: f|C is univalent
    provided no m-1 dimensional affine subspace of R^n
    contains u_0,...,u_m. Whenever 0<m<=n+1 this printed
    condition is equivalent to independence of the edges
    u_1-u_0,...,u_m-u_0. If n+1<m, no such subspace exists:
    the printed condition then holds vacuously, and the
    actual R^0 example with m=2 shows that f|C need not
    be univalent. For m=0 the natural truncation of m-1
    makes the condition false; univalence is then trivial. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  FiniteCoordinates FiniteSpans FiniteSpanSpace FiniteIndependence
  FiniteDimension FiniteBasisComparison FiniteBasisExtension
  GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  AffineSubspaceSpace ConvexHull EuclideanOpenUnitCube CurrentSimplexFrame
  PolyhedralCurrentGenerators DegenerateSimplexPlane
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeInjectivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_independent_widen]: an initial
    segment of an independent family is independent,
    supporting the plane enlargement for 4.1.27, p. 384. *)
Lemma finite_independent_widen (K:fieldType) (V:lmodType K) k N
    (h:(k<=N)%N) (f:'I_N->V):
  finite_independent f->finite_independent (fun i:'I_k=>f (widen_ord h i)).
Proof.
move=>hf c hc i.
pose c' (j:'I_N):K:=if insub (val j) is Some l then c l else 0.
have hc':forall l:'I_k,c' (widen_ord h l)=c l.
  by move=>l;rewrite /c' /= valK.
rewrite -hc';apply:hf.
rewrite (bigID (fun j:'I_N=>(val j<k)%N)) /=.
have hOut: \sum_(j<N|~~(val j<k)%N) c' j*:f j=0.
  by apply:big1=>j hj;rewrite /c' insubN // scale0r.
rewrite hOut addr0 (big_ord_narrow h).
apply:(etrans _ hc);apply:eq_bigr=>l _;by rewrite hc'.
Qed.

(** Source for [independent_grassmann_bound]: an independent
    family inside an element of G(V,k) has at most k members,
    supporting the plane condition of 4.1.27, p. 384. *)
Lemma independent_grassmann_bound (K:fieldType) (V:lmodType K) k
    (W:G V k) l (e:'I_l->V):
  (forall i,grassmann_val W (e i))->finite_independent e->(l<=k)%N.
Proof.
move=>hW he.
have[b hb]:=grassmann_proof W.
pose eW:'I_l->subspace_space (grassmann_val W):=fun i=>subspace_lift (hW i).
have hInd:finite_independent eW.
  move=>c hc;apply:he.
  have h:=congr1 (@subspace_val K V (grassmann_val W)) hc.
  rewrite linear_sum linear0 in h.
  have hs:(\sum_i subspace_val (c i*:eW i))=\sum_i c i*:e i.
    apply:eq_bigr=>i _;rewrite linearZ;congr (_*:_);exact:subspace_liftE.
  by rewrite hs in h.
have h:=@finite_independent_dimension K (finite_basis_vect hb) l eW hInd.
by rewrite finite_basis_dimension card_ord in h.
Qed.

(** Source for [grassmann_ambient_bound]: R^n has no
    subspace of dimension larger than n, supporting the
    vacuous case of the printed condition in 4.1.27, p. 384. *)
Lemma grassmann_ambient_bound (R:realType) n k (W:G (R_n R n) k):(k<=n)%N.
Proof.
have[b hb]:=grassmann_proof W.
have hi:=@finite_independent_map R (Finite.clone 'I_k _)
  (subspace_space (grassmann_val W)) (R_n R n)
  (subspace_inclusion (grassmann_val W)) b
  (@subspace_val_injective R (R_n R n) (grassmann_val W))
  (finite_basis_independent hb).
have h:=@finite_independent_dimension R
  (finite_basis_vect (@coordinate_basisP R n)) k _ hi.
by rewrite finite_basis_dimension card_ord in h.
Qed.

(** Source for [simplex_avoids_codimension_one_planes]: the printed
    condition in 4.1.27, p. 384: no m-1 dimensional affine
    subspace of R^n contains u_0,...,u_m. The dimension m-1
    is the natural predecessor of m. *)
Definition simplex_avoids_codimension_one_planes (R:realType) n m
    (v:'I_(m.+1)->R_n R n):Prop:=
  forall a (W:G (R_n R n) m.-1),~(forall i,affine_coset a W (v i)).

(** Source for [nondegenerate_simplex_avoids_planes]: independent
    edges cannot lie in an m-1 dimensional linear subspace,
    supporting 4.1.27, p. 384, in every ambient dimension. *)
Theorem nondegenerate_simplex_avoids_planes (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (0<m)%N->is_nondegenerate_current_simplex v->
  simplex_avoids_codimension_one_planes v.
Proof.
move=>hm hNon a W hIn.
have hEdge:forall i,grassmann_val W (current_simplex_edge_family v i).
  move=>i;rewrite /current_simplex_edge_family.
  have h1:=hIn (lift ord0 i);have h0:=hIn ord0.
  rewrite /affine_coset /= in h1 h0.
  have->:v (lift ord0 i)-v ord0=(v (lift ord0 i)-a)-(v ord0-a).
    by rewrite opprB addrA subrK.
  exact:subspace_sub h1 h0.
have hBound:=independent_grassmann_bound hEdge hNon.
have hLess:(m.-1<m)%N by rewrite ltn_predL.
by move:hLess;rewrite ltnNge hBound.
Qed.

(** Source for [degenerate_simplex_codimension_one_plane]: if
    m<=n+1 and the edges are dependent, an m-1 dimensional
    affine subspace contains all vertices, supporting 4.1.27,
    p. 384. The plane of smaller dimension from the degenerate
    case is enlarged by an extended basis of R^n. *)
Theorem degenerate_simplex_codimension_one_plane (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (m<=n.+1)%N->~is_nondegenerate_current_simplex v->
  exists a (W:G (R_n R n) m.-1),forall i,affine_coset a W (v i).
Proof.
move=>hmn hDeg.
pose X:=R_n R n.
have[d [A [hd [[a [W hA]] hHull]]]]:=degenerate_simplex_plane_exists hDeg.
have hIn:forall i,affine_coset a W (v i).
  move=>i;rewrite -hA;apply:hHull;apply:convex_hull_includes;by exists i.
have[b hb]:=grassmann_proof W.
pose e (i:'I_d):X:=subspace_val (b i).
have he:finite_independent e.
  exact:(@finite_independent_map R (Finite.clone 'I_d _)
    (subspace_space (grassmann_val W)) X (subspace_inclusion (grassmann_val W)) b
    (@subspace_val_injective R X (grassmann_val W)) (finite_basis_independent hb)).
have[N [hdN [f [hfB hfe]]]]:=@finite_basis_extension R X d e he n
  (@coordinate_basis R n) (@coordinate_basisP R n).
have hN:N=n:=finite_basis_size hfB (@coordinate_basisP R n).
have hmN:(m.-1<=N)%N.
  rewrite hN;move:hmn;by case:m {hd hDeg hHull hIn} v.
have hdm:(d<=m.-1)%N.
  move:hd;by case:m {hmn hmN hDeg hHull hIn} v.
pose g (j:'I_(m.-1)):X:=f (widen_ord hmN j).
have hg:finite_independent g.
  exact:(@finite_independent_widen _ _ _ _ hmN _ (finite_basis_independent hfB)).
pose S:=finite_span_subspace g.
pose W':@G R X m.-1:=@GrassmannSubspace R X m.-1 S
  (ex_intro _ (finite_span_basis g) (finite_span_basisP hg)).
have hContain:forall x,grassmann_val W x->S x.
  move=>x hx.
  have hAll:forall y:subspace_space (grassmann_val W),S (subspace_val y).
    apply:(basis_induction hb)=>[|y z hy hz|c y hy|i].
    - rewrite linear0;exact:subspace_zero.
    - rewrite linearD;exact:subspace_add hy hz.
    - rewrite linearZ;exact:subspace_scale hy.
    - have->:subspace_val (b i)=g (widen_ord hdm i).
        rewrite /g -/(e i) -hfe;congr f;exact:val_inj.
      exact:finite_span_generator.
  have:=hAll (subspace_lift hx);by rewrite subspace_liftE.
exists a,W'=>i;have:=hIn i;rewrite /affine_coset /=;exact:hContain.
Qed.

(** Source for [simplex_avoids_planes_nondegenerate]: the printed
    condition of 4.1.27, p. 384, is equivalent to independence
    of the edges whenever 0<m<=n+1. *)
Theorem simplex_avoids_planes_nondegenerate (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (0<m)%N->(m<=n.+1)%N->
  (simplex_avoids_codimension_one_planes v<->is_nondegenerate_current_simplex v).
Proof.
move=>hm hmn;split;last exact:nondegenerate_simplex_avoids_planes.
move=>hAvoid;have[hNon|hDeg]:=pselect (is_nondegenerate_current_simplex v)=>//.
have[a [W hIn]]:=degenerate_simplex_codimension_one_plane hmn hDeg.
by case:(hAvoid a W hIn).
Qed.

(** Source for [simplex_cube_printed_univalence]: the univalence
    assertion of 4.1.27, p. 384, under its printed affine
    hypothesis, whenever m<=n+1. *)
Theorem simplex_cube_printed_univalence (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (m<=n.+1)%N->simplex_avoids_codimension_one_planes v->
  forall x y:R_n R m,euclidean_open_unit_cube x->euclidean_open_unit_cube y->
    @SimplexCubeParametrisation.value R n m v x=
      @SimplexCubeParametrisation.value R n m v y->x=y.
Proof.
move=>hmn hAvoid.
have[hNon|hDeg]:=pselect (is_nondegenerate_current_simplex v).
  exact:simplex_cube_parametrisation_injective hNon.
have[a [W hIn]]:=degenerate_simplex_codimension_one_plane hmn hDeg.
by case:(hAvoid a W hIn).
Qed.

(** Source for [simplex_avoids_planes_above_dimension]: if n+1<m,
    then R^n has no m-1 dimensional subspace, and the printed
    condition of 4.1.27, p. 384, holds for every vertex family. *)
Theorem simplex_avoids_planes_above_dimension (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  (n.+1<m)%N->simplex_avoids_codimension_one_planes v.
Proof.
move=>hnm a W _;have hBound:=grassmann_ambient_bound W.
move:hnm;rewrite ltnNge;case/negP;move:hBound;by case:m {v W}.
Qed.

(** Source for [simplex_cube_printed_univalence_counterexample]:
    the literal condition of 4.1.27, p. 384, is vacuous for
    m=2 and n=0, but the actual map from the open unit square
    to R^0 identifies two distinct points. *)
Theorem simplex_cube_printed_univalence_counterexample (R:realType):
  exists v:'I_3->R_n R 0,
    simplex_avoids_codimension_one_planes v /\
    exists x y:R_n R 2,euclidean_open_unit_cube x /\
      euclidean_open_unit_cube y /\ x<>y /\
      @SimplexCubeParametrisation.value R 0 2 v x=
        @SimplexCubeParametrisation.value R 0 2 v y.
Proof.
pose v:'I_3->R_n R 0:=fun=>0.
have hHalf:0<(2:R)^-1<1.
  by rewrite invr_gt0 ltr0n /= invf_lt1 ?ltr0n // ltr1n.
have hQuarter:0<(4:R)^-1<1.
  by rewrite invr_gt0 ltr0n /= invf_lt1 ?ltr0n // ltr1n.
pose x:R_n R 2:=[ffun=>2^-1].
pose y:R_n R 2:=[ffun=>4^-1].
exists v;split;first exact:(@simplex_avoids_planes_above_dimension R 0 2 v).
exists x,y;split;first by move=>i;rewrite /x ffunE.
split;first by move=>i;rewrite /y ffunE.
split;last by rewrite (coordinate_zero (_ x)) (coordinate_zero (_ y)).
move/(congr1 (fun z:R_n R 2=>z ord0));rewrite /x /y !ffunE=>/eqP.
by rewrite (inj_eq (@invr_inj R)) eqr_nat.
Qed.
