(** Federer (1969), 4.1.22, p. 379: the original
    additive generated group and real span contain their finite
    integer and real combinations. These public algebraic
    consequences use the existing finite-span containment theorem
    from 1.7.3, p. 29, rather than repeating its proof. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet FiniteSpans InvariantFiniteSpan
  PolyhedralCurrentGenerators PolyhedralCurrentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralCurrentFiniteSums.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation Integral := (@integral_polyhedral_current_class R h2 n m U hU K).
Local Notation Real := (@polyhedral_current_subspace R h2 n m U hU K).

(** Source for [integral_polyhedral_current_natural_multiple]:
    finite repeated addition remains in the original integral
    generated subgroup, supporting 4.1.22, p. 379. *)
Lemma integral_polyhedral_current_natural_multiple (T:C):
  Integral T->forall q:nat,Integral (T*+q).
Proof.
move=>hT;elim=>[|q hQ].
- rewrite mulr0n;exact:integral_polyhedral_current_zero.
- rewrite mulrS;exact:integral_polyhedral_current_add hT hQ.
Qed.

(** Source for [integral_polyhedral_current_integer_multiple]:
    every integer multiple remains in the original integral
    generated subgroup, supporting 4.1.22, p. 379.
    Arbitrary real multiples are reserved for the real span. *)
Theorem integral_polyhedral_current_integer_multiple (T:C):
  Integral T->forall q:int,Integral (q%:~R*:T).
Proof.
move=>hT q;rewrite scaler_int;case:q=>q;rewrite /intmul.
- exact:(@integral_polyhedral_current_natural_multiple T hT q).
- apply:integral_polyhedral_current_negate.
  exact:(@integral_polyhedral_current_natural_multiple T hT q.+1).
Qed.

(** Source for [integral_polyhedral_current_finite_sum]: finite
    sums of the original integral chains remain in the same
    compact index, supporting 4.1.22, p. 379. The empty
    sum is included. *)
Theorem integral_polyhedral_current_finite_sum d (e:'I_d->C):
  (forall i,Integral (e i))->Integral (\sum_i e i).
Proof.
move=>hE;elim/big_rec:_=>[|i T hI hT].
- exact:integral_polyhedral_current_zero.
- exact:integral_polyhedral_current_add (hE i) hT.
Qed.

(** Source for [integral_polyhedral_current_finite_integer_sum]:
    every original finite integer combination belongs to the
    fixed-K integral group, supporting 4.1.22, p. 379. *)
Theorem integral_polyhedral_current_finite_integer_sum d
    (e:'I_d->C) (a:'I_d->int):
  (forall i,Integral (e i))->Integral (\sum_i (a i)%:~R*:e i).
Proof.
move=>hE;apply:integral_polyhedral_current_finite_sum=>i.
exact:(@integral_polyhedral_current_integer_multiple (e i) (hE i) (a i)).
Qed.

(** Source for [polyhedral_current_finite_span_contained]: the
    real span contains every original finite real combination,
    supporting 4.1.22, p. 379. Apply the already proved
    finite-family least-containment law of 1.7.3, p. 29. *)
Theorem polyhedral_current_finite_span_contained d (e:'I_d->C):
  (forall i,Integral (e i))->forall T,in_finite_span e T->Real T.
Proof.
move=>hE.
apply:(@finite_span_subspace_contained R C d e Real)=>i.
exact:integral_polyhedral_current_is_polyhedral (hE i).
Qed.

(** Source for [polyhedral_current_finite_simplex_combination]:
    every finite real combination of the original admissible
    oriented simplexes lies in P_(m,K)(U), supporting
    4.1.22, p. 379. It includes empty families, repeated
    vertices, degree zero and arbitrary real coefficients. *)
Theorem polyhedral_current_finite_simplex_combination d
    (v:'I_d->'I_(m.+1)->X) (a:'I_d->R):
  (forall i,@polyhedral_simplex_vertex_hull R n m (v i)
    `<=` smooth_compact_carrier K)->
  Real (\sum_i a i*:@open_oriented_simplex_current R h2 n m U hU (v i)).
Proof.
move=>hHull.
apply:(@polyhedral_current_finite_span_contained d
  (fun i=>@open_oriented_simplex_current R h2 n m U hU (v i))).
- move=>i;exact:integral_polyhedral_current_generator (hHull i).
- exists a;by [].
Qed.
End PolyhedralCurrentFiniteSums.
