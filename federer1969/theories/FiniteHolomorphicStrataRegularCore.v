(** Federer (1969), 3.4.10, p. 337:
    outside the lower-dimensional strata and holomorphic
    boundaries, the original set agrees locally with
    one top-dimensional holomorphic manifold. Use the corrected
    closure laws of 3.4.12, p. 339, extending 3.4.8(11), p. 327. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric HolomorphicSubmanifoldUP HolomorphicSubmanifoldOpenRestriction
  HolomorphicRegularLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_strata_regular_core]: the
    local regular-part conclusion behind 3.4.10,
    p. 337. The finite closed union of
    the other stratum closures supplies an actual
    neighbourhood on which only the chosen manifold
    remains. No regularity conclusion is assumed. *)
Theorem finite_holomorphic_strata_regular_core (R:realType) n m (J:finType)
    (U A L W:set (coordinate_space (ComplexScalars.C R) n)) (V S G:J->set (coordinate_space (ComplexScalars.C R) n)) (d:J->nat):
  let T:=Topological.clone (real_norm_metric_space
    (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _ in
  @is_holomorphic_regular_locus R n m U A L ->
  @open T W ->W `<=` U ->
  A `&` W=(\bigcup_j S j) `&` W ->
  (forall j,W `<=` V j) ->
  (forall j,(d j<=m)%N /\@is_holomorphic_submanifold R (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) (d j) (S j)) ->
  (forall i j,i<>j ->forall x,S i x ->~S j x) ->
  (forall j,V j `&` @closure T (S j) `<=` S j `|` G j) ->
  forall a,A a ->W a ->(forall j,~G j a) ->
    (forall j,(d j<m)%N ->~S j a) ->L a.
Proof.
move=>T hL hW hWU hEquation hWV hManifold hDisjoint hBoundary a haA haW hNoBoundary hNoLower.
have hUnion:(\bigcup_j S j) a.
  have h:((\bigcup_j S j) `&` W) a by rewrite -hEquation;split.
  exact:h.1.
have [i _ hai]:=hUnion.
have hDimension:d i=m.
  apply/eqP;rewrite eqn_leq (hManifold i).1 /=.
  case:(leqP m (d i))=>// hSmall.
  exfalso;exact:hNoLower i hSmall hai.
pose C:set T:=\bigcup_(j in [set j:J|j!=i]) @closure T (S j).
have hClosed:@closed T C.
  apply:(@closed_bigcup T J [set j:J|j!=i] (fun j=>@closure T (S j))
    (@finite_finset J [set j:J|j!=i]))=>j _.
  exact:closed_closure.
have haNotC:~C a.
  move=>[j hJI hClosure].
  have [hSj|hGj]:=hBoundary j a (conj (hWV j a haW) hClosure).
  - apply:(hDisjoint i j _ a hai hSj).
    move=>hEqual;move/eqP:hJI;apply;exact:esym hEqual.
  - exact:hNoBoundary j hGj.
pose N:set T:=W `&` ~` C.
have hN:@open T N:=openI hW (closed_openC hClosed).
have hSame:A `&` N=S i `&` N.
  apply/seteqP;split.
  - move=>x [hxA [hxW hxNot]];split;last by split.
    have h:((\bigcup_j S j) `&` W) x by rewrite -hEquation;split.
    have [j _ hxSj]:=h.1.
    case:(eqVneq j i)=>hJI;first by rewrite -hJI.
    exfalso;apply:hxNot;exists j;first exact:hJI.
    exact:subset_closure hxSj.
  - move=>x [hxSi [hxW hxNot]];split;last by split.
    have h:(A `&` W) x.
      rewrite hEquation;split;last exact:hxW.
      by exists i.
    exact:h.1.
apply/(hL a);split;first exact:haA.
exists N;split;first exact:hN.
split;first by split.
split;first by move=>x hx;exact:hWU x hx.1.
rewrite hSame -hDimension.
exact:holomorphic_submanifold_open_restriction (hManifold i).2 hN.
Qed.
