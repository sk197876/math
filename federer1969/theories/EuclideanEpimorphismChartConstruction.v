(** Federer (1969), 3.1.3(3), p. 213: existence of the linear
    change of coordinates adapted to an epimorphism. Extend its independent
    coordinate covectors to a dual basis, and evaluate that basis.
    This private witness is used only by the opaque sealing module. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates Hom
  TensorUP LinearBasis FiniteDualDimension FiniteIndependence
  FiniteBasisExtension FiniteBasisComparison EuclideanLinearMaps
  EuclideanEpimorphismChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Coordinates.
Variable R : realType.
Variables n m : nat.
Variable p : {linear R_n R n -> R_n R m}.
(** Source for [epimorphism_coordinate_witness]: the covectors of alpha
    in the coordinate-change step of Federer 3.1.3(3), p. 213. *)
Definition epimorphism_coordinate_witness i (x : R_n R n) : R^o := p x i.
(** Source for [epimorphism_coordinate_witness_linear]: linearity of
    those covectors, supporting Federer 3.1.3(3), p. 213. *)
Lemma epimorphism_coordinate_witness_linear i : linear (epimorphism_coordinate_witness i).
Proof. by move=> a x y; rewrite /epimorphism_coordinate_witness linearP !ffunE. Qed.
HB.instance Definition _ i := GRing.isLinear.Build R (R_n R n) R^o *:%R
  (epimorphism_coordinate_witness i) (epimorphism_coordinate_witness_linear i).
End Coordinates.

Section Evaluation.
Variable R : realType.
Variable n : nat.
Variable b : 'I_n -> Hom (R_n R n) R^o.
(** Source for [dual_coordinate_witness]: evaluation in the extended
    dual basis, constructing beta in Federer 3.1.3(3), p. 213. *)
Definition dual_coordinate_witness (x : R_n R n) : R_n R n := [ffun i => b i x].
(** Source for [dual_coordinate_witness_linear]: supporting linearity
    of the coordinate change in Federer 3.1.3(3), p. 213. *)
Lemma dual_coordinate_witness_linear : linear dual_coordinate_witness.
Proof. by move=> a x y; apply/ffunP=> i; rewrite /dual_coordinate_witness !ffunE; exact: hom_linear. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (R_n R n) (R_n R n) *:%R
  dual_coordinate_witness dual_coordinate_witness_linear.
(** Source for [dual_coordinate_witness_injective]: a full dual basis
    separates vectors, supporting the isomorphism in Federer 3.1.3(3), p. 213. *)
Lemma dual_coordinate_witness_injective : is_basis b -> injective dual_coordinate_witness.
Proof.
move=> hb x y hxy.
have he i : b i x=b i y.
  have := congr1 (fun z : R_n R n=>z i) hxy.
  by rewrite /dual_coordinate_witness !ffunE.
have hall := basis_linear_ext hb
  (GRing.Linear.clone _ _ _ _ (hom_evaluate x) _)
  (GRing.Linear.clone _ _ _ _ (hom_evaluate y) _) he.
apply/ffunP=> i.
exact: hall (hom_of_linear (GRing.Linear.clone _ _ _ _
  (epimorphism_coordinate_witness (linear_id (R_n R n)) i) _)).
Qed.
End Evaluation.

(** Source for [euclidean_epimorphism_chart_exists]: existence of beta
    in Federer 3.1.3(3), p. 213. The dimension inequality follows from
    independence of the pulled-back coordinate covectors; it is not an
    additional hypothesis. Empty coordinate blocks are included. *)
Theorem euclidean_epimorphism_chart_exists (R : realType) n m
    (p : {linear R_n R n -> R_n R m}) : (forall y, exists x, p x=y) ->
  exists w : {hmn : (m<=n)%N &
    ({linear R_n R n -> R_n R n} * {linear R_n R n -> R_n R n})%type},
    is_euclidean_epimorphism_chart p (projT1 w) (projT2 w).1 (projT2 w).2.
Proof.
move=> hp.
pose e i := hom_of_linear (GRing.Linear.clone _ _ _ _ (epimorphism_coordinate_witness p i) _).
pose v i := projT1 (cid (hp (@coordinate_basis R m i))).
have hv i : p (v i)=@coordinate_basis R m i := projT2 (cid (hp (@coordinate_basis R m i))).
have he : finite_independent e.
  apply: (@finite_independent_separating R 'I_m (Hom (R_n R n) R^o) e
    (fun i=>GRing.Linear.clone _ _ _ _ (hom_evaluate (v i)) _))=> i j.
  change (p (v i) j=if i==j then 1 else 0).
  by rewrite hv /coordinate_basis ffunE eq_sym.
have [l [hml [b [hb hbe]]]] := finite_basis_extension he (dual_basisP (@coordinate_basisP R n)).
have hln : l=n := finite_basis_size hb (dual_basisP (@coordinate_basisP R n)).
subst l.
pose f := GRing.Linear.clone _ _ _ _ (dual_coordinate_witness b) _.
have hf : injective f := dual_coordinate_witness_injective hb.
have [g [hfg hgf]] := euclidean_linear_inverse hf.
exists (existT _ hml (f,g)); constructor=> // x i.
change (dual_coordinate_witness b x (widen_ord hml i)=p x i).
by rewrite /dual_coordinate_witness ffunE hbe.
Qed.
