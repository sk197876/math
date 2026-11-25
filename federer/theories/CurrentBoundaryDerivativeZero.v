(** Federer (1969), 4.1.7, pp. 356–357: zero
    coordinate derivatives imply zero boundary.
    This supporting consequence of the original
    coordinate boundary formula applies to E^n. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms CurrentSpaces
  CurrentBoundary CurrentBoundaryCoordinates CurrentContraction CurrentConstantFields CurrentDirectionalDerivative
  CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentDegreeTransportDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentBoundaryDerivativeZero.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun j=>@current_space R h2 n U hU j).
Local Notation Tr := (fun a b (h:a=b)=>@current_degree_transport R h2 n U hU a b h).
Local Notation dir := (fun j v=>@current_directional_derivative R h2 n j U hU v).

(** Source for [current_coordinate_derivatives_zero_boundary]:
    the original boundary sum is zero when
    every D_j T is zero, supporting Federer
    4.1.7, pp. 356–357, including an empty
    coordinate family. *)
Theorem current_coordinate_derivatives_zero_boundary (T:C m.+1):
  (forall j,dir m.+1 (@coordinate_basis R n j) T=0) ->
  @current_boundary R h2 n m U hU T=0.
Proof.
move=>hDir.
have h:=@current_boundary_coordinate_formula R h2 n m U hU
  (Tr _ _ (esym (add1n m)) T).
rewrite current_degree_transport_roundtrip in h.
rewrite h.
have hSum:(\sum_j @current_contraction R h2 n 1%N m U hU
    (@current_constant_form R h2 n U hU 1%N (euclidean_coordinate_form j))
    (dir (1+m) (@coordinate_basis R n j) (Tr _ _ (esym (add1n m)) T)))=0.
  apply:big1=>j _.
  rewrite current_degree_transport_directional (hDir j) !linear0;by [].
by rewrite hSum oppr0.
Qed.
End CurrentBoundaryDerivativeZero.
