(** Federer (1969), 3.3.4, p. 288: the three original
    alternatives for a plane through a prescribed centre.
    All limit operators are the existing independently specified
    sealed order operators; the alternatives themselves are
    predicates, not additional assumptions or selected witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric EuclideanProjectionSpace StructureCone ExtendedRealBounds
  PositiveRadiusLimits PositiveRightOrderLimit StructureProjectionKernel
  StructureConeDensityFormula StructureConeDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_plane_radial_supremum]: the inner
    radius supremum in alternatives (1) and (2) of
    Federer 3.3.4, p. 288, using the original plane
    and original set A with the printed r^(-m)s^(-m) weights. *)
Definition structure_plane_radial_supremum (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (V:G (R_n R n) k) (delta s:R): \bar R:=
  extended_real_sup [set v|exists r:R,(0<r<delta) /\
    v=(phi (A `&` structure_cone V a r%:E s)*((r^-1)^+m)%:E*((s^-1)^+m)%:E)%E].

(** Source for [structure_plane_zero_growth]: alternative
    (1) of Federer 3.3.4, p. 288: for some
    positive delta, the ordinary right-hand limit of
    the full radius supremum is zero. *)
Definition structure_plane_zero_growth (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):Prop:=
  exists delta:R,0<delta /\ positive_right_extended_order_limit
    (structure_plane_radial_supremum m phi A a V delta) 0%E.

(** Source for [structure_plane_infinite_growth]: alternative
    (2) of Federer 3.3.4, p. 288: at every
    positive delta the actual positive-aperture upper limit
    of the original radius supremum is infinity. *)
Definition structure_plane_infinite_growth (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):Prop:=
  forall delta:R,0<delta ->positive_radius_upper_limit
    (structure_plane_radial_supremum m phi A a V delta)=+oo%E.

(** Source for [structure_plane_accumulation]: alternative
    (3) of Federer 3.3.4, p. 288: the centre
    lies in the closure of points of A other than
    itself in the original affine plane a+V. *)
Definition structure_plane_accumulation (R:realType) n k
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):Prop:=
  closure [set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=a /\ grassmann_val V (x-a)] a.

(** Source for [structure_plane_trichotomy]: the disjunction
    of the three explicitly numbered alternatives of Federer
    3.3.4, p. 288. Its almost-everywhere truth for
    the actual Grassmann probability must be proved later. *)
Definition structure_plane_trichotomy (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):Prop:=
  structure_plane_zero_growth m phi A a V \/
  structure_plane_infinite_growth m phi A a V \/structure_plane_accumulation A a V.

(** Source for [structure_plane_kernel_densityE]: the
    original-plane upper growth in alternative (2) of
    Federer 3.3.4, p. 288, agrees at an actual
    kernel plane with the sealed 3.3.2 density. *)
Lemma structure_plane_kernel_densityE (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (p:euclidean_projection_space R n m) delta:
  positive_radius_upper_limit
    (structure_plane_radial_supremum m phi A a (structure_projection_kernel hmn p) delta)=
  structure_cone_density hmn phi A delta (a,p).
Proof. exact:esym (structure_cone_density_bookE hmn phi A delta (a,p)). Qed.
