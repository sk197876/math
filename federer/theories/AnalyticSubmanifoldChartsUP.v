(** Federer (1969), 3.1.24, p. 240: analytic replacements in
    3.1.19, p. 231. The four alternative local
    specifications (2)–(5). Equivalence with the straightening
    definition is an obligation proved separately, not a defining axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness InnerConvex NormDifferentialUP
  NormClassOneUP NormRegularity NormMetric NormDiffeomorphismUP
  LinearRankUP OrthogonalMaps AdjointUP EuclideanSubmanifoldUP NormAnalyticUP AnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Charts.
Variable R:realType.
Variable n:nat.
Local Notation E d:=(R_n R d).
Local Notation N d:=(inner_norm (@euclidean_inner_productP R d)).
Local Notation hN d:=(inner_norm_real_norm (@euclidean_inner_productP R d)).

(** Source for [has_analytic_regular_level_charts]: analytic condition (2), Federer 3.1.24, p. 240, referring to
    3.1.19, p. 231: B is locally a level set of an analytic map with
    constant rank n-mu. D is its actual class-one differential field. The local bound mu<=n
    expresses the nonnegative codimension; natural subtraction would
    otherwise truncate an impossible negative dimension to zero. *)
Definition has_analytic_regular_level_charts mu (B:set (E n)) :=
  forall b, B b -> exists i (T:set (E n)) (f:E n->E i) (D:E n->Hom (E n) (E i)),
    norm_domain_interior (N n) T b /\ (mu<=n)%N /\ (n-mu<=i)%N /\
    @norm_analytic R (E n) (E i) (N n) (N i) (hN n) (hN i) T f /\ is_norm_class_one_field (N n) (N i) T f D /\
    B `&` T=[set x|T x /\ f x=f b] /\
    forall x, T x -> has_linear_rank (D x) (n-mu).

(** Source for [has_analytic_open_parametrisations]: analytic condition
    (3), Federer 3.1.24, p. 240, referring to 3.1.19, p. 231: an analytic map of constant rank mu,
    with m>=mu, maps its open parameter subsets to relatively open
    subsets of B and has b in its image. The range inclusion is the
    explicit meaning of mapping into relatively open subsets of B. *)
Definition has_analytic_open_parametrisations mu (B:set (E n)) :=
  forall b, B b -> exists m (Q:set (E m)) (f:E m->E n) (D:E m->Hom (E m) (E n)),
    (mu<=m)%N /\ @norm_analytic R (E m) (E n) (N m) (N n) (hN m) (hN n) Q f /\
    is_norm_class_one_field (N m) (N n) Q f D /\
    (forall x, Q x -> B (f x)) /\ (f @` Q) b /\
    (forall x, Q x -> has_linear_rank (D x) mu) /\
    forall W:set (E m), W `<=` Q -> @open [the topologicalType of real_norm_metric_space (hN m)] W ->
      @relatively_open_set [the topologicalType of real_norm_metric_space (hN n)] B (f @` W).

(** Source for [has_analytic_convex_coordinates]: analytic condition (4), Federer 3.1.24, p. 240, referring to
    Federer 3.1.19, p. 231: phi:T->V and psi:V->T are analytic,
    V is convex and open, psi(V)=B intersect T and phi psi=id.
    Openness is already part of the two class predicates. *)
Definition has_analytic_convex_coordinates mu (B:set (E n)) :=
  forall b, B b -> exists (T:set (E n)) (V:set (E mu))
    (phi:E n->E mu) (psi:E mu->E n),
    norm_domain_interior (N n) T b /\ is_inner_convex V /\
    @norm_analytic R (E n) (E mu) (N n) (N mu) (hN n) (hN mu) T phi /\ @norm_analytic R (E mu) (E n) (N mu) (N n) (hN mu) (hN n) V psi /\
    (forall x, T x -> V (phi x)) /\ (forall u, V u -> T (psi u)) /\
    psi @` V=B `&` T /\ forall u, V u -> phi (psi u)=u.

(** Source for [has_analytic_orthogonal_graphs]: analytic condition (5), Federer 3.1.24, p. 240, referring to
    Federer 3.1.19, p. 231: p is orthogonal, injective on B intersect T,
    p(B intersect T)=p(T) is convex, the inverse psi is analytic and
    Dpsi[p(b)]=p*. The orthogonal injection j and adjoint equation
    specify p* without selecting its implementation. *)
Definition has_analytic_orthogonal_graphs mu (B:set (E n)) :=
  forall b, B b -> exists (T:set (E n)) (p:{linear E n->E mu})
    (j:{linear E mu->E n}) (psi:E mu->E n),
    norm_domain_interior (N n) T b /\
    is_orthogonal_map (@euclidean_inner_product R mu) (@euclidean_inner_product R n) j /\
    is_adjoint (@euclidean_inner_product R mu) (@euclidean_inner_product R n) j p /\
    (forall x y, B x /\ T x -> B y /\ T y -> p x=p y -> x=y) /\
    p @` (B `&` T)=p @` T /\ is_inner_convex (p @` T) /\
    @norm_analytic R (E mu) (E n) (N mu) (N n) (hN mu) (hN n) (p @` T) psi /\
    (forall u, (p @` T) u -> B (psi u) /\ T (psi u)) /\
    (forall u, (p @` T) u -> p (psi u)=u) /\
    (forall x, B x /\ T x -> psi (p x)=x) /\
    has_norm_differential (N mu) (N n) (p @` T) psi (p b) (hom_of_linear j).
End Charts.
