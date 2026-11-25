(** Federer (1969), 3.4.12, p. 339: the actual square
    graph has two local holomorphic sheets over the punctured
    plane, with relatively open images and exhaustive fibres.
    Its one connected component still has a two-to-one projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import TensorUP Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  HolomorphicUP HolomorphicLinear TopologicalProductMaps ComplexSquareCoverObstruction
  ComplexSquareCoverFibres ComplexSquareLocalCoverUP ComplexSquareLocalCoverExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Graph.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation M:=(real_norm_metric_space hN).
Local Notation V:=(@complex_square_punctured_graph R).

(** Source for [original_complex_square_graph_local_cover]: the
    actual polynomial model for the covering replacement on p. 339,
    3.4.12. Both scalar coordinates of every section are
    holomorphic; their images are relatively open in the original
    graph and every original inverse image is exhausted. *)
Theorem original_complex_square_graph_local_cover (w:C):w<>0 ->
  exists W:set M,exists s:'I_2->C->C,
    is_original_complex_square_local_cover w W s /\
    @is_holomorphic R C^o C^o N N hN hN W idfun /\
    forall i,exists O:set (M*M),@open [the topologicalType of (M*M)%type] O /\
      (fun v:M=>((v,s i v):(M*M)%type)) @` W=V `&` O.
Proof.
move=>hW.
have [W [s hCover]]:=@original_complex_square_local_cover_exists R w hW.
have [hOpen [hCentre [hNonzero [hHOL [hRoots [hDistinct [hExhaust hImages]]]]]]]:=hCover.
exists W,s;split;first exact:hCover.
split.
- pose Id:Hom C^o C^o:=hom_of_linear (linear_id C^o).
  have hBound:@norm_bounded_linear R CR CR N N (complex_hom_real Id).
    exists 1;split;first exact:ler01.
    move=>z;change (is_true (N z<=1*N z));by rewrite mul1r.
  apply:(@holomorphic_bounded_linear R C^o C^o N N hN hN W Id _ hBound).
  move=>v hv;apply:(@norm_domain_interior_neighbourhood R CR N hN W v).2.
  have h:=hOpen;rewrite openE in h;exact:h v hv.
- move=>i;have [O [hO hImage]]:=hImages i.
  exists ((fun p:M*M=>p.2) @^-1` O);split.
  + exact:(@open_comp [the topologicalType of (M*M)%type] M (fun p:M*M=>p.2) O
      (fun p _=>@second_projection_continuous M M p) hO).
  + apply/seteqP;split.
    * move=>p [v hv <-];split.
      -- split.
         ++ move=>hZero;change (s i v=0) in hZero.
            apply:(hNonzero v hv);by rewrite -(hRoots i v hv) hZero expr0n.
         ++ exact:esym (hRoots i v hv).
      -- have h:( [set z:M|z<>0] `&` O) (s i v) by rewrite -hImage;exists v.
         exact:h.2.
    * move=>p [[hSecond hEquation] hInO].
      have hMember:(s i @` W) p.2 by rewrite hImage;split.
      have [v hv hValue]:=hMember.
      have hFirst:v=p.1 by rewrite -(hRoots i v hv) hValue -hEquation.
      exists v;first exact:hv.
      by rewrite hValue hFirst -surjective_pairing.
Qed.

(** Source for [original_complex_square_cover_component_obstruction]:
    the original connected double cover disproves a componentwise
    projection-homeomorphism conclusion in the complex adaptation of
    3.4.8(10), 3.4.12, p. 339. Local sheets, rather than
    a global ordering, give the proved replacement. *)
Theorem original_complex_square_cover_component_obstruction:
  connected V /\
  (forall w:C,w<>0 ->exists W:set M,exists s:'I_2->C->C,
    is_original_complex_square_local_cover w W s) /\
  exists a b:M*M,V a /\V b /\a<>b /\connected_component V a b /\a.1=b.1.
Proof.
split;first exact:complex_square_graph_connected.
split;first exact:original_complex_square_local_cover_exists.
exact:complex_square_graph_component_projection_not_injective.
Qed.
End Graph.
