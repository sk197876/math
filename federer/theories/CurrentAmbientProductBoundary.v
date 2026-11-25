(** Federer (1969), 4.1.11, p. 366: the
    original Cartesian prism boundary, transported only
    through equal full-domain presentations. Reuse all
    positive-degree cases of 4.1.8, p. 360, with
    the first factor an arbitrary one-current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentBoundary CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentDegreeTransportIdentity CurrentDomainTransport CurrentDomainTransportDegree
  CurrentAmbientCartesianProduct CurrentCartesianBoundaryPositive CurrentCartesianBoundaryFirstZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentAmbientProductBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n) (hFull m) (hFull n)).
Local Notation CA := (fun k=>@current_space R h2 m (Full m) (hFull m) k).
Local Notation CB := (fun k=>@current_space R h2 n (Full n) (hFull n) k).
Local Notation CTr := (fun k=>@current_domain_transport R h2 (m+n)%N AB hAB
  (Full (m+n)%N) (@current_cartesian_full_domain R m n) (hFull (m+n)%N) k).
Local Notation Product := (fun i j=>@current_ambient_cartesian_product R h2 m n i j).

(** Source for [current_ambient_product_boundary_point]:
    boundary(S times T)=(boundary S) times T when
    S has degree one and T has degree zero, supporting
    Federer 4.1.11, p. 366. No boundary of a
    zero-current is formed. *)
Theorem current_ambient_product_boundary_point (S:CA 1%N) (T:CB 0%N):
  @current_boundary R h2 (m+n)%N 0%N (Full (m+n)%N) (hFull (m+n)%N)
    (Product 1%N 0%N S T)=
  Product 0%N 0%N (@current_boundary R h2 m 0%N (Full m) (hFull m) S) T.
Proof.
rewrite /current_ambient_cartesian_product -current_domain_transport_boundary.
have hOld:=@current_cartesian_boundary_first_zero R h2 m n
  (Full m) (Full n) (hFull m) (hFull n) 0%N S T.
rewrite current_degree_transport_identity in hOld.
by rewrite hOld.
Qed.

(** Source for [current_ambient_product_boundary_positive]:
    boundary(S times T)=(boundary S) times T minus
    S times boundary T for one-dimensional S and
    positive-dimensional T, supporting Federer 4.1.11,
    p. 366. The original arbitrary currents remain allowed. *)
Theorem current_ambient_product_boundary_positive j (S:CA 1%N) (T:CB j.+1):
  @current_boundary R h2 (m+n)%N j.+1 (Full (m+n)%N) (hFull (m+n)%N)
    (Product 1%N j.+1 S T)=
  Product 0%N j.+1 (@current_boundary R h2 m 0%N (Full m) (hFull m) S) T-
  Product 1%N j S (@current_boundary R h2 n j (Full n) (hFull n) T).
Proof.
rewrite /current_ambient_cartesian_product -current_domain_transport_boundary.
have hOld:=@current_cartesian_boundary_positive R h2 m n
  (Full m) (Full n) (hFull m) (hFull n) 0%N j S T.
rewrite !current_degree_transport_identity expr1 scaleN1r in hOld.
rewrite hOld.
exact:(linB (hom_linear (CTr j.+1)) _ _).
Qed.
End CurrentAmbientProductBoundary.
