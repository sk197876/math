(** Federer (1969), 3.2.9, p. 247: specify
    the countable Borel cover and its global
    Lipschitz maps before proving existence. Cartesian
    targets are represented by the canonical isometric
    block coordinates of 2.6.5, pp. 119–120. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  CoordinateProjection EuclideanBlockCoordinates NormDifferentialUP TopologicalBorel LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [surjective_differential_locus]: the
    set {x:im Df(x)=R^n} in Federer
    3.2.9, p. 247. Both an actual
    differential and surjectivity are required; no
    value is assigned outside its actual domain. *)
Definition surjective_differential_locus (R:realType) m n
    (f:R_n R m->R_n R n):set (R_n R m):=
  [set a|exists D:Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f a D /\
    forall y,exists x,D x=y].

(** Source for [is_coordinate_inverse_piece]: the
    Borel set E, orthogonal coordinate projection p,
    and two global Lipschitz maps u,v of
    Federer 3.2.9, p. 247. The first
    map agrees with (f,p) on E and
    the second is its left inverse there.
    No extension witness is assumed by this predicate. *)
Definition is_coordinate_inverse_piece (R:realType) m n
    (f:R_n R m->R_n R n) (E:set (R_n R m)):Prop:=
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] E /\
  exists p:{linear R_n R m->R_n R ((m-n)%N)},O_star p /\
  exists (u:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R ((n+(m-n))%N)))
    (v:inner_metric_space (@euclidean_inner_productP R ((n+(m-n))%N))->
      inner_metric_space (@euclidean_inner_productP R m)),
    is_metric_lipschitz setT u /\ is_metric_lipschitz setT v /\
    forall x,E x -> u x=euclidean_block_join (f x,p x) /\ v (u x)=x.

(** Source for [is_coordinate_inverse_cover]: the
    countable Borel cover of the full-target-rank
    differential locus in Federer 3.2.9, p. 247.
    Every member has the printed global maps and
    projection; actual coverage and all existence laws
    are mathematical obligations of the later theorem. *)
Definition is_coordinate_inverse_cover (R:realType) m n
    (f:R_n R m->R_n R n) (G:set (set (R_n R m))):Prop:=
  countable G /\ surjective_differential_locus f `<=` (\bigcup_(E in G) E) /\
    forall E,G E -> is_coordinate_inverse_piece f E.
