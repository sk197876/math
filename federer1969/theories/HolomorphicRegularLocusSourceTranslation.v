(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    the original regular-locus criterion is preserved
    by actual source translation. Use the
    proved translation of holomorphic manifold charts
    in both directions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicSubmanifoldUP
  HolomorphicRegularLocusUP HolomorphicSubmanifoldSourceTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_regular_locus_source_translation]: the
    same original regular points in translated
    coordinates, needed for the all-centre singular-part
    assertions of 3.4.10, p. 337.
    Neighbourhoods, domain containment and holomorphic manifold
    dimension are all retained explicitly. *)
Theorem holomorphic_regular_locus_source_translation (R:realType) n m
    (U S L:set (coordinate_space (ComplexScalars.C R) n)) (c:coordinate_space (ComplexScalars.C R) n):
  @is_holomorphic_regular_locus R n m U S L ->
  @is_holomorphic_regular_locus R n m [set x|U (x-c)] [set x|S (x-c)] [set x|L (x-c)].
Proof.
move=>hL.
pose X:=coordinate_space (ComplexScalars.C R) n.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose u:=fun x:T=>(x-c:T).
pose v:=fun x:T=>(x+c:T).
have hU:continuous u.
  have hSame:u=(fun x:T=>(-c+x:T)) by apply:funext=>x;rewrite /u addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hV:continuous v.
  have hSame:v=(fun x:T=>(c+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hUV:cancel v u by move=>x;rewrite /u /v addrK.
have hVU:cancel u v by move=>x;rewrite /u /v subrK.
move=>b;split.
- move/(hL (u b))=>[hbS [V [hOpen [hbV [hInside hManifold]]]]].
  split;first exact:hbS.
  exists (u @^-1` V);split;first exact:(@open_comp T T u V (fun x _=>hU x) hOpen).
  split;first exact:hbV.
  split;first by move=>x hx;exact:hInside (u x) hx.
  exact:(@holomorphic_submanifold_source_translation R n m (S `&` V) c hManifold).
- move=>[hbS [W [hOpen [hbW [hInside hManifold]]]]].
  apply/(hL (u b));split;first exact:hbS.
  exists (v @^-1` W);split;first exact:(@open_comp T T v W (fun x _=>hV x) hOpen).
  split;first by change (W (v (u b)));rewrite hVU.
  split.
  + move=>x hx;have h:=hInside (v x) hx.
    change (U (u (v x))) in h;by rewrite hUV in h.
  + have hOriginal:=@holomorphic_submanifold_source_translation R n m
      ((u @^-1` S) `&` W) (-c) hManifold.
    have hSame:[set x|((u @^-1` S) `&` W) (x-(-c))]=S `&` (v @^-1` W).
      apply:funext=>x.
      change ((S ((x-(-c))-c) /\W (x-(-c)))=(S x /\W (x+c))).
      by rewrite opprK addrK.
    by rewrite hSame in hOriginal.
Qed.
