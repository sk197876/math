(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332:
    the actual original equation matrix gives
    independent differentials on the transverse
    basis. Apply the biorthogonal matrix connection. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom FiniteIndependence FiniteArrowCovectorIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_equation_transverse_independence]:
    W' nonzero and delta nonzero make
    Df_(m+1),...,Df_n linearly independent,
    3.4.12, p. 339, extending 3.4.8(10), pp. 331–332. The
    exact original prefix kernel and dual
    suffix coordinates are retained. *)
Theorem field_equation_transverse_independence (R:fieldType) (X Y:lmodType R)
    (index:finType) (first:index) (P:Hom X Y) (xi:index->Hom X R^o)
    (v:index->X) (D:index->Hom X R^o) (delta wD:R) (tD:index->R):
  (forall j,P (v j) = 0) ->
  (forall i j,xi i (v j) = if i==j then 1 else 0) ->
  (forall j u,P u = 0 ->D j u = if j==first then wD*xi first u else
    delta*xi j u-tD j*xi first u) ->
  delta!=0 ->wD!=0 ->finite_independent D.
Proof.
move=>hV hDual hDirections hDelta hWD.
apply:(@finite_arrow_covectors_independent R X index first D v delta hDelta).
- by rewrite (@hDirections first (v first) (hV first)) eqxx hDual eqxx mulr1.
- move=>i j hJ.
  have hFirstOther:xi first (v j) = 0 by rewrite hDual eq_sym (negbTE hJ).
  rewrite (@hDirections i (v j) (hV j)) hFirstOther.
  case hCase:(i==first).
  + have hEqual:i = first:=eqP hCase;subst i.
    by rewrite eq_sym (negbTE hJ) !mulr0.
  + by rewrite hDual mulr0 subr0.
Qed.
