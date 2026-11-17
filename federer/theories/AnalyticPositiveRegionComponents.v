(** Federer (1969), 3.4.8(11), p. 333:
    the complete critical-maximum component-counting argument.
    Local finiteness of the lower-dimensional critical
    variety is the induction input. The
    proof constructs the actual critical maxima
    and uses their actual connected components
    as a finite family of markers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity NormAnalyticUP NormAnalyticLocal
  CompactLocalComponentFiniteness ConnectedComponentsFiniteFromMarkers ConnectedNonzeroBoundaryAvoidance
  NormPositiveCriticalMaximum AnalyticCriticalConnectedConstancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PositiveComponents.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Variables (A S K:set X) (f:X->R^o) (D:X->Hom X R^o).
Local Notation H:=([set x|A x /\ forall v,D x v = 0]).

(** Source for [analytic_positive_region_finite_components]:
    finite critical components near a compact
    ball imply finitely many positive components,
    3.4.8(11), p. 333. Local finiteness
    is the preceding dimension-induction input;
    the rest of the printed maximum
    argument is proved here. *)
Theorem analytic_positive_region_finite_components:
  (0<n)%N ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f ->
  (forall x,A x ->has_norm_differential NX (fun z:R^o=>`|z|) A f x (D x)) ->
  @compact T K ->S `<=` K ->K `<=` A ->
  (forall x,S x ->0<f x) ->
  (forall a,S a ->forall x,@closure T (@connected_component T S a) x ->
    ~@interior T (@connected_component T S a) x ->f x = 0) ->
  (forall a,K a ->exists U:set X,@open T U /\ U a /\
    finite_set (@connected_component T H @` (H `&` U))) ->
  finite_set (@connected_component T S @` S).
Proof.
move=>hN hAnalytic hD hK hSK hKA hPositive hBoundary hLocal.
pose F:=@connected_component T H @` (H `&` K).
have hFinite:finite_set F:=@compact_local_component_finiteness T H K hK hLocal.
apply:(@components_finite_from_connected_markers T S F hFinite).
- move=>B [a [_ _] <-];exact:component_connected.
- move=>a ha.
  pose C:=@connected_component T S a.
  have hCa:C a:=connected_component_refl ha.
  have hCS:C `<=` S:=@connected_component_sub T S a.
  have hCK:C `<=` K by move=>x hx;exact:hSK x (hCS x hx).
  have hZeroBoundary:forall x,@closure T C x ->~@interior T C x ->f x = 0.
    exact:hBoundary a ha.
  have [b [hCb [hPositiveB hCriticalB]]]:=@norm_positive_critical_maximum R X NX hNX A C K f D a
    (norm_class_continuous (norm_analytic_class_all_orders hAnalytic 0%N)) hD hK hCK hKA
    hCa (hPositive a ha) hZeroBoundary.
  have hKb:K b:=hCK b hCb.
  have hHb:H b by split;[exact:hKA b hKb|exact:hCriticalB].
  pose B:=@connected_component T H b.
  have hBb:B b:=connected_component_refl hHb.
  have hBH:B `<=` H:=@connected_component_sub T H b.
  have hBA:B `<=` A by move=>x hx;exact:(hBH x hx).1.
  have hConstant:forall x,B x ->f x = f b.
    move=>x hx;exact:(@analytic_critical_connected_constancy R n A B f D hN hAnalytic hBA
      (@component_connected T H b) hD (fun z hz=>(hBH z hz).2) x b hx hBb).
  have hNonzero:f b<>0 by move=>hZero;move:hPositiveB;rewrite hZero ltxx.
  exists B;split.
  + by exists b;first split.
  + split;first by exists b.
    exact:(@connected_nonzero_boundary_avoidance T R^o B C f b
      (@component_connected T H b) hBb hCb hNonzero hConstant hZeroBoundary).
Qed.
End PositiveComponents.
