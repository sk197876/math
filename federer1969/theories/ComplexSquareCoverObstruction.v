(** Federer (1969), 3.4.12, p. 339: the prescribed complex
    covering argument replaces the real ordered-sheet argument.
    The actual equation z squared equals w has a connected graph
    over the punctured plane, while its coordinate projection is
    two-to-one. This model prevents a false global ordered-sheet
    conclusion in the complex adaptation of 3.4.8(10). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric ScalarRestriction ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormOpenDomainLaws HolomorphicUP HolomorphicLinear HolomorphicProduct
  NormAnalyticLocal NormRegularity NormClassZeroTopology TopologicalProductMaps ContinuousCommonPair ComplexPuncturedPlaneConnected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Obstruction.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation M:=(real_norm_metric_space hN).

(** Source for [complex_square_map_holomorphic]: the actual
    polynomial z squared is holomorphic with the original norm,
    supporting the covering model for 3.4.12, p. 339. *)
Lemma complex_square_map_holomorphic:
  @is_holomorphic R C^o C^o N N hN hN setT (fun z=>z^+2).
Proof.
pose identity:Hom C^o C^o:=hom_of_linear (linear_id C^o).
have hBound:@norm_bounded_linear R CR CR N N (complex_hom_real identity).
  exists 1;split;first exact:ler01.
  move=>z;change (is_true (N z<=1*N z));by rewrite mul1r.
have hIdentity:=@holomorphic_bounded_linear R C^o C^o N N hN hN setT identity
  (fun z _=>@norm_full_domain_interior R CR N z) hBound.
have hProduct:=@holomorphic_product R C^o N hN setT idfun idfun hIdentity hIdentity.
have hMap:(fun z:C=>z^+2)=(fun z:C=>z*z) by apply:funext=>z;rewrite expr2.
by rewrite hMap.
Qed.

(** Source for [complex_square_map_continuous]: the actual
    holomorphic polynomial is continuous in the original norm
    topology, 3.4.12, p. 339. *)
Lemma complex_square_map_continuous:continuous (fun z:M=>(z^+2:M)).
Proof.
have hClass:=norm_analytic_class_all_orders complex_square_map_holomorphic.1 0%N.
move=>z;exact:(@norm_class_zero_continuous_at R CR CR N N hN hN setT
  (fun z=>z^+2) z (norm_class_continuous hClass) Logic.I).
Qed.

(** Source for [complex_square_punctured_graph]: the actual
    punctured polynomial graph w=z squared in the original complex
    plane product, supporting 3.4.12, p. 339. *)
Definition complex_square_punctured_graph:set (M*M):=
  [set p|p.2<>0 /\p.1=p.2^+2].
Local Notation V:=complex_square_punctured_graph.

(** Source for [complex_square_graph_connected]: the original
    punctured graph is connected, since its parameter is the
    actual punctured complex plane, 3.4.12, p. 339. *)
Theorem complex_square_graph_connected:connected V.
Proof.
pose f:M->M*M:=fun z=>(z^+2,z).
have hIdentity:continuous (@idfun M) by move=>z;exact:cvg_id.
have hContinuous:continuous f:=@continuous_common_domain_pair M M M (fun z=>z^+2) idfun
  complex_square_map_continuous hIdentity.
have hSame:f @` [set z:M|z<>0]=V.
  apply/seteqP;split.
  - move=>p [z hz <-];by split.
  - move=>p [hz hEquation];exists p.2;first exact:hz.
    by rewrite /f -hEquation -surjective_pairing.
rewrite -hSame.
exact:(connected_continuous_connected (@complex_punctured_plane_connected R) (continuous_subspaceT hContinuous)).
Qed.

(** Source for [complex_square_graph_component_projection_not_injective]:
    one actual connected component contains the distinct points
    (1,1) and (1,-1) with the same first coordinate. Hence the
    original projection cannot be a homeomorphism on that component,
    3.4.12, p. 339. *)
Theorem complex_square_graph_component_projection_not_injective:
  exists a b:M*M,V a /\V b /\a<>b /\
    connected_component V a b /\a.1=b.1.
Proof.
pose a:M*M:=(1,1);pose b:M*M:=(1,-1).
have hOne:(1:C)<>0 by apply/eqP;exact:oner_neq0.
have hNegative:(-1:C)<>0 by apply/eqP;rewrite oppr_eq0;exact:oner_neq0.
have hA:V a by split;first exact:hOne;by rewrite expr1n.
have hB:V b by split;first exact:hNegative;by rewrite expr2 mulNr mulrN opprK mul1r.
have hDifferent:a<>b.
  move=>hEqual;have hValue:=congr1 (fun p:M*M=>ComplexScalars.re p.2) hEqual.
  change (ComplexScalars.re (1:C)=ComplexScalars.re (-1:C)) in hValue.
  rewrite re_neg (complex_re_one (ComplexScalars.laws R)) in hValue.
  have hPositive:0<(1:R)+1 by rewrite addr_gt0.
  by rewrite {1}hValue addNr ltxx in hPositive.
have hWhole:connected_component V a=V.
  apply/seteqP;split;first exact:connected_component_sub.
  exact:(@connected_component_max (M*M)%type V V a hA (@subset_refl (M*M)%type V) complex_square_graph_connected).
exists a,b;split;first exact:hA.
split;first exact:hB.
split;first exact:hDifferent.
split;last by [].
by rewrite hWhole.
Qed.
End Obstruction.
