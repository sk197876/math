(** Federer (1969), 3.2.28, printed pp. 263–267: submanifolds
    of suitable finite-dimensional inner-product spaces, including
    Hom, exterior powers and symmetric powers. An actual isometric
    identification transports the definition of 3.1.19. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations InnerProductUP
  FiniteInnerChartUP EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_inner_submanifold]: a mu-dimensional class-k
    submanifold in a finite inner-product ambient space, Federer
    3.2.28, pp. 263–267. This is precisely the existing 3.1.19
    straightening definition in an actual isometric Euclidean chart.
    Existence of both the ambient chart and every local straightening
    must be proved; no construction or existence axiom is hidden here. *)
Definition is_inner_submanifold (R:realType) (V:lmodType R)
    (B:V->V->R) mu k (S:set V):=
  exists n (e:Hom (R_n R n) V) (p:Hom V (R_n R n)),
    is_finite_inner_chart B e p /\
    @is_euclidean_submanifold R n mu k (p @` S).
